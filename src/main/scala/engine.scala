package faba.engine

import scala.collection.mutable

object `package` {
  implicit class LatticeOps[Val](x: Val)(implicit l: Lattice[Val]) {
    @inline def &(y: Val): Val =
      l.meet(x, y)

    @inline def meet(y: Val): Val =
      l.meet(x, y)

    @inline def |(y: Val): Val =
      l.join(x, y)

    @inline def join(y: Val): Val =
      l.join(x, y)
  }

  // sum of products
  type SoP[T] = Set[Component[T]]

  implicit class ResultOps[Id, Val](r1: Result[Id, Val])(implicit l: Lattice[Val]) {
    val top: Val = l.top
    @inline def join(r2: Result[Id, Val]): Result[Id, Val] = (r1, r2) match {
      case (Final(`top`), _) =>
        Final(`top`)
      case (_, Final(`top`)) =>
        Final(`top`)
      case (Final(v1), Final(v2)) =>
        Final(v1 join v2)
      case (Final(v1), Pending(v2, comps2)) =>
        Pending(v1 join v2, comps2)
      case (Pending(v1, comps1), Final(v2)) =>
        Pending(v1 join v2, comps1)
      case (Pending(v1, comps1), Pending(v2, comps2)) =>
        Pending(v1 join v2, comps1 union comps2)
    }
  }
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

case class ELattice[E](bot: E, top: E) extends Lattice[E]

case class Component[Id](touched: Boolean, ids: Set[Id]) {
  def remove(id: Id) =
    Component(touched, ids - id)

  def remove_!(id: Id) =
    if (ids.contains(id)) {
      Component(true, ids - id)
    } else {
      this
    }

  def isEmpty =
    ids.isEmpty

  def isEmpty_! =
    touched && ids.isEmpty
}

sealed trait Result[+Id, Val]
case class Final[Val](value: Val) extends Result[Nothing, Val]
case class Pending[Id, Val](infinum: Val, delta: SoP[Id]) extends Result[Id, Val]

case class Equation[Id, Val](id: Id, rhs: Result[Id, Val])

trait StableAwareId[K] {
  val stable: Boolean
  def mkUnstable: K
  def mkStable: K
}

final class Solver[K <: StableAwareId[K], V](implicit lattice: Lattice[V]) {
  type Solution = (K, V)
  val top = lattice.top
  val bot = lattice.bot

  private val dependencies = mutable.HashMap[K, Set[K]]()
  private val pending = mutable.HashMap[K, Pending[K, V]]()
  private val moving = mutable.Queue[Solution]()
  private var solved = Map[K, V]()

  def this(equations: List[Equation[K, V]])(implicit lattice: Lattice[V]) {
    this()
    equations.foreach(addEquation)
  }

  def addEquation(equation: Equation[K, V]): Unit =
    equation.rhs match {
      case Final(value) =>
        moving enqueue (equation.id -> value)
      case Pending(`top`, _) =>
        moving enqueue (equation.id -> top)
      case p@Pending(_, sop) =>
        for (trigger <- sop.map(_.ids).flatten) {
          dependencies(trigger) = dependencies.getOrElse(trigger, Set()) + equation.id
        }
        pending(equation.id) = p
    }

  def solve(): Map[K, V] = {
    while (moving.nonEmpty) {
      val (ident, value) = moving.dequeue()
      solved = solved + (ident -> value)

      // intricate logic here (null -> ... inference is a bit strange for now - optimistic assumption)
      val toPropagate: List[(K, V)] =
        if (ident.stable)
          List((ident, value), (ident.mkUnstable, value))
        else
          List((ident.mkStable, value), (ident, top))

      for {
        (pId, pValue) <- toPropagate
        dIds <- dependencies.remove(pId)
        dId <- dIds
        pend <- pending.remove(dId)
      } substitute(pend, pId, pValue) match {
        case Final(v) => moving enqueue (dId -> v)
        case p@Pending(_, _) => pending(dId) = p
      }
    }

    for ((id, _) <- pending)
      solved = solved + (id -> top)
    pending.clear()
    solved
  }

  private def substitute(pending: Pending[K, V], id: K, value: V): Result[K, V] =
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
