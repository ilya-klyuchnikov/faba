package faba.calls

import java.util.Date

import faba.data._

import org.objectweb.asm.Opcodes

import scala.annotation.tailrec
import scala.collection.immutable.Queue
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
  // whether a class is an interface
  def interface_? = (access & Opcodes.ACC_INTERFACE) != 0
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

  // fqn -> set of inheritors (for classes) / set of implementors (for interfaces)
  private var childrenMap = Map[String, Set[String]]()

  /**
   * calculates all class inheritors of this class/interface
   * @param className org.objectweb.asm.tree.ClassNode#name
   * @return all inheritors
   */
  private def inheritors(className: String): Set[String] = {
    @tailrec
    def _inheritors(queue: Queue[String], queued: Set[String], acc: Set[String]): Set[String] = {
      if (queue.isEmpty)
        acc
      else {
        var queued1 = queued
        var (current, queue1) = queue.dequeue
        for {child <- childrenMap.getOrElse(current, Set()) if !queued(child)} {
          queued1 = queued1 + child
          queue1 = queue1.enqueue(child)
        }
        _inheritors(queue1, queued1, acc + current)
      }

    }
    _inheritors(Queue(className), Set(className), Set())
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
        for {found <- findConcreteMethodDeclaration(method, methods)}
          return Some(convertToMethod(found))
    }
    None
  }

  // O(n), n - number of the methods in the hierarchy
  def resolveUpward(method: Method, ownerResolveInfo: ResolvedClassInfo): Option[Method] = {
    for {candidateOwner <- ownerResolveInfo.hierarchyLine}
      classMethods.get(candidateOwner) match {
        case None =>
          return None
        case Some(methods) =>
          for {found <- findConcreteMethodDeclaration(method, methods)}
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
    val preciseMethodInfo: Option[MethodInfo] =
      classMethods.get(method.internalClassName).flatMap(candidates => findConcreteMethodDeclaration(method, candidates))
    val effectivelyFinalMethod =
      preciseMethodInfo.exists(!isEffectivelyOverridableMethod(_))
    if (effectivelyFinalMethod)
      Set(method)
    else
      for {
        implementationName <- inheritors(method.internalClassName)
        implementation <- resolved.get(implementationName)
        resolvedMethod <- resolveUpward(method, implementation)
      } yield resolvedMethod
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

  // TODO - it callKey should be associated with a solver
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
  def buildClassHierarchy() {
    println(s"${new Date()} buildClassHierarchy START")
    for ((className, classInfo) <- classInfos) {
      if (CallUtils.notInterface(classInfo.access))
        resolved.update(className, ResolvedClassInfo(classInfo, hierarchy(className), allInterfaces(className)))

      val superName: String =
        if (classInfo.interface_?) null else classInfo.superName
      if (superName != null)
        childrenMap += superName -> (childrenMap.getOrElse(superName, Set()) + classInfo.name)
      for (interfaceName <- classInfo.interfaces)
        childrenMap += interfaceName -> (childrenMap.getOrElse(interfaceName, Set()) + classInfo.name)
    }
    println(s"${new Date()} buildClassHierarchy END")
  }

  /**
   * Traverses all calls in RHS of equations and resolve them into a set of concrete calls
   * assuming that the world is closed.
   *
   * @return mapping of calls into existing Upward Keys
   */
  def resolveCalls(): Map[Key, Set[Key]] = {
    // TODO - a cache should be built at this stage
    println(s"${new Date()} RESOLVE calls START")
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
    println(s"${new Date()} RESOLVE calls END")
    result
  }

  /**
   * Traverses all hierarchy and for each overridable (non stable methods) constructs a set of concrete method it may resolve in runtime.
   * During this stage a set of different caches are built.
   * @return a map from overridable methods to a set of concrete methods
   */
  def bindOverridableMethods(): Map[Method, Set[Method]] = {
    println(s"${new Date()} BIND OVERRIDABLE START")
    var result = Map[Method, Set[Method]]()
    for {(className, methodInfos) <- classMethods } {
      for {methodInfo <- methodInfos if isEffectivelyOverridableMethod(methodInfo)} {
        val method = Method(className, methodInfo.name, methodInfo.desc)
        val resolved = resolveDownward(method)
        result += (method -> resolved)
      }
    }
    println(s"${new Date()} BIND OVERRIDABLE END")
    result
  }

  private def isNotAbstractMethod(method: MethodInfo): Boolean =
    (method.access & Opcodes.ACC_ABSTRACT) == 0

  private def isEffectivelyOverridableMethod(method: MethodInfo): Boolean = {
    import Opcodes._
    val methodAcc = method.access
    (method.name != "<init>") &&
      (methodAcc & ACC_PRIVATE) == 0 &&
      (methodAcc & ACC_STATIC) == 0 &&
      (methodAcc & ACC_FINAL) == 0 &&
      (method.classInfo.access & ACC_FINAL) == 0
  }

  private def findConcreteMethodDeclaration(call: Method, candidates: Iterable[MethodInfo]): Option[MethodInfo] =
    candidates.find {info => isNotAbstractMethod(info) && info.name == call.methodName && info.desc == call.methodDesc}

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
