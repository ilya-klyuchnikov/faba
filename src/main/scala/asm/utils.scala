package faba.asm

import org.objectweb.asm.Type

object Utils {
  def isReferenceType(tp: Type): Boolean = {
    val sort = tp.getSort
    sort == Type.OBJECT || sort == Type.ARRAY
  }

  def isBooleanType(tp: Type): Boolean = {
    Type.BOOLEAN_TYPE == tp
  }

  def getSizeFast(desc: String): Int =
    desc.charAt(0) match {
      case 'J' | 'D' => 2
      case _ => 1
    }

  def getReturnSizeFast(methodDesc: String): Int =
    methodDesc.charAt(methodDesc.indexOf(')') + 1) match {
      case 'J' | 'D' => 2
      case _ => 1
    }
}
