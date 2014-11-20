package faba.calls

import faba.data.Method

case class ClassInfo(access: Int, name: String, superName: String, interfaces: List[String])

/**
 * Support for inference with hierarchy.
 * All methods are quite specific, read documentation carefully.
 */
class CallResolver {

  var indexing = true

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
    ???
  }

  /**
   * Build hierarchy info. Call this method when indexing is completed.
   *
   */
  def buildHierarchy(): Unit = ???

}
