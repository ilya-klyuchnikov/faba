package faba.calls

import java.util.Date

import faba.data._

import org.objectweb.asm.Opcodes

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
 * Class info available at indexing phase (in class file of a current file, without resolve)
 * @param access     (org.objectweb.asm.tree.ClassNode#access)
 * @param name       (org.objectweb.asm.tree.ClassNode#name)
 * @param superName  (org.objectweb.asm.tree.ClassNode#superName)
 * @param interfaces (org.objectweb.asm.tree.ClassNode#interfaces)
 */
case class ClassInfo(access: Int, name: String, superName: String, interfaces: List[String]) {
  val stable = (access & Opcodes.ACC_FINAL) != 0
}

/**
 * Declaration site method info available at indexing phase.
 *
 * @param classInfo info of class owner
 * @param access    (org.objectweb.asm.tree.ClassNode#access)
 * @param name      (org.objectweb.asm.tree.ClassNode#name)
 * @param desc      (org.objectweb.asm.tree.ClassNode#desc)
 */
case class MethodInfo(classInfo: ClassInfo, access: Int, name: String, desc: String)

/**
 * Aggregated class info after resolve.
 *
 * @param classInfo     class info before resolve
 * @param hierarchyLine hierarchy line (from this to Object)
 * @param interfaces    a set of all interfaces this class implements
 */
case class ResolvedClassInfo(classInfo: ClassInfo, hierarchyLine: List[String], interfaces: Set[String])

/**
 * Support for inference with hierarchy.
 * All methods are quite specific, read documentation carefully.
 */
class CallResolver {

  // information collected during indexing
  private val classInfos = mutable.HashMap[String, ClassInfo]()
  // declarations of methods for a class
  private val classMethods = mutable.HashMap[String, mutable.Set[MethodInfo]]()
  // encountered calls
  private val calls = mutable.Set[Key]()
  // resolved class info
  private val resolved = mutable.HashMap[String, ResolvedClassInfo]()

  /**
   * Calculates all class inheritors of this class.
   * Includes class itself.
   * Doesn't include interfaces for now.
   *
   * @param className org.objectweb.asm.tree.ClassNode#name
   * @return all concrete inheritors
   */
  private def children(className: String): Set[ResolvedClassInfo] = {
    // TODO - cache it or build a map during resolve
    var classes = Set[ResolvedClassInfo]()
    for ((_, info) <- resolved if info.hierarchyLine.contains(className) || info.interfaces.contains(className))
      classes = classes + info
    classes
  }

  /**
   * Used for resolving INVOKESTATIC and INVOKESPECIAL
   * @param method method invoked via INVOKESTATIC or INVOKESPECIAL instruction
   * @return concrete method or None if method is not implemented yet in hierarchy
   */
  def resolveUpward(method: Method): Option[Method] = {
    for {
      ownerResolveInfo <- resolved.get(method.internalClassName)
      candidateOwner <- ownerResolveInfo.hierarchyLine
    } classMethods.get(candidateOwner) match {
      case None =>
        return None
      case Some(methods) =>
        for {found <- findMethodDeclaration(method, methods)}
          return Some(convertToMethod(found))
    }
    None
  }

  def resolveUpward(method: Method, ownerResolveInfo: ResolvedClassInfo): Option[Method] = {
    for {candidateOwner <- ownerResolveInfo.hierarchyLine}
      classMethods.get(candidateOwner) match {
        case None =>
          return None
        case Some(methods) =>
          for {found <- findMethodDeclaration(method, methods)}
            return Some(convertToMethod(found))
      }
    None
  }

  def convertToMethod(methodInfo: MethodInfo): Method =
    Method(methodInfo.classInfo.name, methodInfo.name, methodInfo.desc)

  /**
   * Used for resolving of INVOKEINTERFACE and INVOKEVIRTUAL
   * @param method method invoked via INVOKEINTERFACE and INVOKEVIRTUAL instruction
   * @return all concrete method that can be called in run time
   */
  def resolveDownward(method: Method): Set[Method] = {
    var resolvedMethods = Set[Method]()
    for {implementation <- children(method.internalClassName)
         resolvedMethod <- resolveUpward(method, implementation)}
      resolvedMethods = resolvedMethods + resolvedMethod
    resolvedMethods
  }

  /**
   * Add class info.
   * @param classInfo info from indexing phase
   */
  def addClassDeclaration(classInfo: ClassInfo) {
    classInfos.update(classInfo.name, classInfo)
    classMethods.update(classInfo.name, mutable.Set[MethodInfo]())
  }

  /**
   * Adds method info
   * @param methodInfo info from indexing phase
   */
  def addMethodDeclaration(methodInfo: MethodInfo) {
    classMethods(methodInfo.classInfo.name) += methodInfo
  }

  def addCall(key: Key) {
    calls += key
  }

  /**
   * "At once" resolve.
   *
   * It materializes all classes and methods.
   * Builds the "hierarchy line" of classes for each class,
   * Builds the set of interface a class implements for each class.
   */
  def resolveHierarchy() {
    // building class hierarchy
    for ((className, classInfo) <- classInfos if CallUtils.notInterface(classInfo.access))
      resolved.update(className, ResolvedClassInfo(classInfo, hierarchy(className), allInterfaces(className)))
  }

  /**
   * Traverses all calls in RHS of equations and resolve them into a set of concrete calls
   * assuming that the world is closed.
   *
   * @return mapping of calls into existing Upward Keys
   */
  def resolveCalls(): Map[Key, Set[Key]] = {
    println(s"${new Date()} RESOLVE START")
    var result = Map[Key, Set[Key]]()
    for (call <- calls) {
      val method = call.method
      val ownerName = method.internalClassName
      val resolved: Set[Method] = classInfos.get(ownerName) match {
        case None =>
          //println(s"warning {faba.calls.CallResolver.resolveCalls}: $call is not resolved")
          Set()
        case Some(ownerInfo) =>
          if (call.resolveDirection == ResolveDirection.Upward)
            resolveUpward(call.method).toSet
          else
            resolveDownward(method)
      }
      result += (call -> resolved.map(m => call.copy(method = m, resolveDirection = ResolveDirection.Upward)))
    }
    println(s"${new Date()} RESOLVE END")
    result
  }

  private def isStableMethod(owner: ClassInfo, key: Key): Boolean = {
    import Opcodes._
    val call = key.method
    val acc = findMethodDeclaration(key.method, classMethods.getOrElse(owner.name, Set())).map(_.access).getOrElse({/*println(s"xxx: $key");*/ 0})
    owner.stable || (call.methodName == "<init>") || (acc & ACC_FINAL) != 0 || (acc & ACC_PRIVATE) != 0 || (acc & ACC_STATIC) != 0
  }

  private def findMethodDeclaration(call: Method, candidates: Iterable[MethodInfo]): Option[MethodInfo] =
    candidates.find {info => info.name == call.methodName && info.desc == call.methodDesc}

  /**
   * Builds a hierarchy of parents for a class in a linear order.
   *
   * @param className class for which hierarchy is built
   * @return hierarchy of the class
   */
  private def hierarchy(className: String): List[String] = {
    @tailrec
    def _hierarchy(name: String, acc: ListBuffer[String]): List[String] = classInfos.get(name) match {
      case None =>
        //println(s"warning {faba.calls.CallResolver.hierarchy}: $name is referenced, but not found")
        acc.toList
      case Some(classInfo) =>
        val superName = classInfo.superName
        if (superName == null)
          acc.toList
        else {
          acc += superName
          _hierarchy(superName, acc)
        }
    }
    _hierarchy(className, ListBuffer(className))
  }

  /**
   * Calculates all interfaces implemented by a class.
   *
   * @param className class name
   * @return all interfaces implemented by this class
   */
  private def allInterfaces(className: String): Set[String] = {
    @tailrec
    def _allInterfaces(queue: Set[String], traversed: Set[String], acc: Set[String]): Set[String] = {
      queue.headOption match {
        case None =>
          acc
        case Some(name) =>
          classInfos.get(name) match {
            case None =>
              //println(s"warning {faba.calls.CallResolver.allInterfaces}: $name is referenced, but not found")
              acc
            case Some(classInfo) =>
              val interfaces = classInfo.interfaces.toSet
              _allInterfaces(queue.tail ++ (interfaces -- traversed), traversed + name, acc ++ interfaces)
          }
      }
    }
    _allInterfaces(Set(className), Set(), Set())
  }
}

/**
 * Helper methods
 */
object CallUtils {
  import Opcodes._

  /**
   * True if a class not an interface.
   * @param access (org.objectweb.asm.tree.ClassNode#access)
   */
  def notInterface(access: Int) =
    (access & ACC_INTERFACE) == 0

  def callResolveDirection(opCode: Int) = opCode match {
    case INVOKEINTERFACE | INVOKEVIRTUAL =>
      ResolveDirection.Downward
    case INVOKESTATIC | INVOKESPECIAL =>
      ResolveDirection.Upward
  }

  def specializeCallResolveDirection(resolveDirection: ResolveDirection.Value, callToThis: Boolean) =
    if (callToThis) ResolveDirection.Upward else resolveDirection
}
