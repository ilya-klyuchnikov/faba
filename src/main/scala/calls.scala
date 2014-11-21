package faba.calls

import faba.data.Method

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

// class info got at indexing phase
case class ClassInfo(access: Int, name: String, superName: String, interfaces: List[String])

/**
 * Support for inference with hierarchy.
 * All methods are quite specific, read documentation carefully.
 */
class CallResolver {

  var indexing = true

  // information collected during indexing
  private val classInfos = mutable.HashMap[String, ClassInfo]()

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
   * @param classInfo info from indexing
   */
  def addInfo(classInfo: ClassInfo) {
    require(indexing, "addInfo may be")
    classInfos.update(classInfo.name, classInfo)
  }

  /**
   * Build hierarchy info. Call this method when indexing is completed.
   *
   * It materializes all classes and methods.
   * Builds the "hierarchy line" of classes for each class,
   * Builds the set of interface a class implements for each class.
   */
  def buildHierarchy() {
    indexing = false
  }

  /**
   * Builds a hierarchy of parents for a class in a linear order (not including class itself).
   *
   * @param className class for which hierarchy is built
   * @param acc alreadhy built hierarchy
   * @return hierarchy of the class
   */
  @tailrec
  private def hierarchy(className: String, acc: ListBuffer[String] = ListBuffer()): List[String] = {
    classInfos.get(className) match {
      case None =>
        println(s"warning: $className is referenced, but not found")
        acc.toList
      case Some(classInfo) =>
        val superName = classInfo.superName
        if (superName == null)
          acc.toList
        else {
          acc += superName
          hierarchy(superName, acc)
        }

    }
  }

}
