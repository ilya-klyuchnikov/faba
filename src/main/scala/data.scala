package faba.data

import faba.engine.ELattice

case class Method(className: String, methodName: String, methodDesc: String) {
  override def toString = s"$className $methodName$methodDesc"
}

// analysis direction information
sealed trait ADirection
case class In(paramIndex: Int) extends ADirection
case class InOut(paramIndex: Int, in: Values.Value) extends ADirection
case object Out extends ADirection

case class AKey(method: Method, direction: ADirection) {
  override def toString = direction match {
      case Out => s"$method"
      case In(index) => s"$method #$index"
      case InOut(index, _) => s"$method #$index"
  }
}

object Values extends Enumeration {
  val Bot, NotNull, Null, True, False, Top = Value
}

object Nullity extends Enumeration {
  val NotNull, Nullable = Value
}

object `package` {
  implicit val contractValuesLattice = ELattice(Values)
  implicit val nullityLattice = ELattice(Nullity)
}
