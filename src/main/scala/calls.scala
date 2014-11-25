package faba.calls

import faba.data.Method
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
case class ClassInfo(access: Int, name: String, superName: String, interfaces: List[String])

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
  private val methodUsages = mutable.Set[Method]()
  // resolved class info
  private val resolved = mutable.HashMap[String, ResolvedClassInfo]()

  /**
   * Calculates all concrete inheritors of this class.
   * Includes class itself (if it is concrete).
   *
   * @param className org.objectweb.asm.tree.ClassNode#name
   * @return all concrete inheritors
   */
  private def allConcreteInheritors(className: String): Set[String] = ???

  /**
   * Resolves a method for a class in which given method should definitely exist
   *
   * @param method method invoked via INVOKESTATIC or INVOKESPECIAL instruction
   * @return resolved method
   */
  private def resolveConcrete(method: Method): Method = ???

  /**
   * Used for resolving INVOKESTATIC and INVOKESPECIAL
   * @param method method invoked via INVOKESTATIC or INVOKESPECIAL instruction
   * @return concrete method or None if method is not implemented yet in hierarchy
   */
  def resolveBottomUp(method: Method): Method =
    resolveConcrete(method)

  /**
   * Used for resolving of INVOKEINTERFACE and INVOKEVIRTUAL
   * @param method method invoked via INVOKEINTERFACE and INVOKEVIRTUAL instruction
   * @return all concrete method that can be called in run time
   */
  def resolveTopDown(method: Method): Set[Method] =
    allConcreteInheritors(method.internalClassName).map {
      concreteClass => resolveConcrete(method.copy(internalClassName = concreteClass))
    }


  /**
   * Add class info.
   * @param classInfo info from indexing phase
   */
  def addClassInfo(classInfo: ClassInfo) {
    classInfos.update(classInfo.name, classInfo)
    classMethods.update(classInfo.name, mutable.Set[MethodInfo]())
  }

  /**
   * Adds method info
   * @param methodInfo info from indexing phase
   */
  def addMethodInfo(methodInfo: MethodInfo) {
    classMethods(methodInfo.classInfo.name) += methodInfo
  }

  def addMethodUsage(method: Method) {
    methodUsages += method
  }

  /**
   * "At once" resolve.
   *
   * It materializes all classes and methods.
   * Builds the "hierarchy line" of classes for each class,
   * Builds the set of interface a class implements for each class.
   */
  def resolve() {
    // building resolve info only for classes (not interfaces)
    for ((className, classInfo) <- classInfos if CallUtils.notInterface(classInfo.access))
      resolved.update(className, ResolvedClassInfo(classInfo, hierarchy(className), allInterfaces(className)))
  }

  /**
   * Builds a hierarchy of parents for a class in a linear order (not including class itself).
   *
   * @param className class for which hierarchy is built
   * @return hierarchy of the class
   */
  private def hierarchy(className: String): List[String] = {
    @tailrec
    def _hierarchy(name: String, acc: ListBuffer[String] = ListBuffer()): List[String] = {
      classInfos.get(name) match {
        case None =>
          println(s"warning: $name is referenced, but not found")
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
    }
    _hierarchy(className)
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
              println(s"warning: $name is referenced, but not found")
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
  /**
   * True if a class not an interface.
   * @param access (org.objectweb.asm.tree.ClassNode#access)
   */
  def notInterface(access: Int) =
    (access & Opcodes.ACC_INTERFACE) == 0
}
