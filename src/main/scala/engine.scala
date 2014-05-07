package faba.engine

import scala.collection.mutable

object `package` {
  implicit class LatticeOps[Val](x: Val)(implicit l: Lattice[Val]) {
    @inline def &(y: Val): Val =
      l.meet(x, y)

    @inline def |(y: Val): Val =
      l.join(x, y)
  }

  // sum of products
  type SoP[T] = Set[Component[T]]
}

// complete finite lattice
trait Lattice[T] extends PartialOrdering[T] {
  val top: T
  val bot: T

  // |,  union
  final def join(x: T, y: T): T =
    (x, y) match {
      case (`bot`, _) => y
      case (_, `bot`) => x
      case (`top`, _) => top
      case (_, `top`) => top
      case _ => if (equiv(x, y)) x else top
    }

  // &, intersection
  final def meet(x: T, y: T): T =
    (x, y) match {
      case (`top`, _) => y
      case (_, `top`) => x
      case (`bot`, _) => bot
      case (_, `bot`) => bot
      case _ => if (equiv(x, y)) x else bot
    }

  final override def equiv(x: T, y: T): Boolean =
    x == y

  final override def tryCompare(x: T, y: T): Option[Int] =
    (x, y) match {
      case (`bot`, `bot`) => Some(0)
      case (_, `bot`) => Some(1)
      case (`bot`, _) => Some(-1)
      case (`top`, `top`) => Some(0)
      case (_, `top`) => Some(-1)
      case (`top`, _) => Some(1)
      case (_, _) => if (equiv(x, y)) Some(0) else None
    }

  final override def lteq(x: T, y: T): Boolean =
    tryCompare(x, y).getOrElse(1) <= 0
}

case class ELattice[E<:Enumeration](enum: E) extends Lattice[E#Value] {
  type Val = E#Value
  val bot: Val = enum.values.firstKey
  val top: Val = enum.values.lastKey
}

case class Component[Id](touched: Boolean, ids: Set[Id]) {
  def remove(id: Id) =
    Component(touched, ids - id)

  def remove_!(id: Id) =
    Component(true, ids - id)

  def isEmpty =
    ids.isEmpty

  def isEmpty_! =
    touched && ids.isEmpty
}

sealed trait Result[+Id, Val]
case class Final[Val](value: Val) extends Result[Nothing, Val]
case class Pending[Id, Val](infinum: Val, delta: SoP[Id]) extends Result[Id, Val]

case class Equation[Id, Val:Lattice](id: Id, rhs: Result[Id, Val])

final class Solver[Id, Val:Lattice] {
  type Solution = (Id, Val)
  val top = implicitly[Lattice[Val]].top
  val bot = implicitly[Lattice[Val]].bot

  private val dependencies =
    mutable.HashMap[Id, Set[Id]]()

  private val pending =
    mutable.HashMap[Id, Pending[Id, Val]]()
  private val moving =
    mutable.Queue[Solution]()
  private var solved =
    Map[Id, Val]()

  def this(equations: List[Equation[Id, Val]]) {
    this()
    equations.foreach(addEquation)
  }

  def addEquation(equation: Equation[Id, Val]): Unit =
    equation.rhs match {
      case Final(value) =>
        moving enqueue (equation.id -> value)
      case p@Pending(_, sop) =>
        for (trigger <- sop.map(_.ids).flatten) {
          dependencies(trigger) = dependencies.getOrElse(trigger, Set()) + equation.id
        }
        pending(equation.id) = p
    }

  def solve(): Map[Id, Val] = {
    while (moving.nonEmpty) {
      val (ident, value) = moving.dequeue()
      solved = solved + (ident -> value)
      for {
        dIds <- dependencies.remove(ident)
        dId <- dIds
        pend <- pending.remove(dId)
      } substitute(pend, ident, value) match {
        case Final(v) => moving enqueue (dId -> v)
        case p@Pending(_, _) => pending(dId) = p
      }
    }

    for ((id, _) <- pending)
      solved = solved + (id -> top)
    pending.clear()
    solved
  }

  private def substitute(pending: Pending[Id, Val], id: Id, value: Val): Result[Id, Val] =
    value match {
      case `bot` =>
        val delta = pending.delta.filterNot(_.ids(id))
        if (delta.isEmpty) Final(pending.infinum)
        else Pending(pending.infinum, delta)
      case `top` =>
        val delta = pending.delta.map(_.remove(id)).filterNot(_.isEmpty_!)
        if (delta.exists(_.isEmpty)) Final(`top`)
        else if (delta.isEmpty) Final(pending.infinum)
        else Pending(pending.infinum, delta)
      case _ =>
        pending.infinum | value match {
          case `top` =>
            Final(`top`)
          case infinum =>
            val delta = pending.delta.map(_.remove_!(id)).filterNot(_.isEmpty)
            if (delta.isEmpty) Final(infinum)
            else Pending(infinum, delta)
        }
    }
}
