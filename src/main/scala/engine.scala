package faba.engine

import faba.analysis.LimitReachedException

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
  type SoP[K, V] = Set[Component[K, V]]

  implicit class ResultOps[Id, Val](r1: Result[Id, Val])(implicit l: Lattice[Val]) {
    val top: Val = l.top
    @inline def join(r2: Result[Id, Val]): Result[Id, Val] = (r1, r2) match {
      case (Final(`top`), _) =>
        Final(`top`)
      case (_, Final(`top`)) =>
        Final(`top`)
      case (Final(v1), Final(v2)) =>
        Final(v1 join v2)
      case (Final(v1), Pending(comps2)) =>
        Pending(comps2 + Component(v1, Set()))
      case (Pending(comps1), Final(v2)) =>
        Pending(comps1 + Component(v2, Set()))
      case (Pending(comps1), Pending(comps2)) =>
        Pending(comps1 union comps2)
    }
  }
}

// complete finite lattice
trait Lattice[T] {
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

  final def equiv(x: T, y: T): Boolean =
    x == y
}

case class ELattice[E](bot: E, top: E) extends Lattice[E]

case class Component[Id, V](v: V, ids: Set[Id])

sealed trait Result[+Id, Val]
case class Final[Val](value: Val) extends Result[Nothing, Val]
case class Pending[Id, Val](delta: SoP[Id, Val]) extends Result[Id, Val] {
  if (delta.map(_.ids.size).sum > 30) throw new LimitReachedException
}

case class Equation[Id, Val](id: Id, rhs: Result[Id, Val])

trait StableAwareId[K] {
  val stable: Boolean
  def mkUnstable: K
  def mkStable: K
}

class Solver[K <: StableAwareId[K], V](val doNothing: Boolean)(implicit lattice: Lattice[V]) {

  type Solution = (K, V)
  val top = lattice.top
  val bot = lattice.bot

  private val dependencies = mutable.HashMap[K, Set[K]]()
  private val pending = mutable.HashMap[K, Pending[K, V]]()
  private val moving = mutable.Queue[Solution]()
  private var solved = Map[K, V]()

  def this(equations: List[Equation[K, V]])(implicit lattice: Lattice[V]) {
    this(false)
    equations.foreach(addEquation)
  }

  def addEquation(equation: Equation[K, V]): Unit =
    if (doNothing) return
    else
    equation.rhs match {
      case Final(value) =>
        moving enqueue (equation.id -> value)
      case Pending(sum) => normalize(sum) match {
        case Final(value) =>
          moving enqueue (equation.id -> value)
        case p@Pending(comps) =>
          for (trigger <- comps.map(_.ids).flatten) {
            dependencies(trigger) = dependencies.getOrElse(trigger, Set()) + equation.id
          }
          pending(equation.id) = p
      }
    }

  def solve(): Map[K, V] = {
    while (moving.nonEmpty) {
      val (ident, value) = moving.dequeue()
      solved = solved + (ident -> value)

      val toPropagate: List[(K, V)] =
        if (ident.stable)
          List((ident, value), (ident.mkUnstable, value))
        else
          List((ident.mkStable, value), (ident, mkUnstableValue(value)))

      for {
        (pId, pValue) <- toPropagate
        dIds <- dependencies.remove(pId)
        dId <- dIds
        pend <- pending.remove(dId)
      } substitute(pend, pId, pValue) match {
        case Final(v) => moving enqueue (dId -> v)
        case p@Pending(_) => pending(dId) = p
      }
    }

    /*
    for ((id, _) <- pending)
      solved = solved + (id -> top)
    */
    pending.clear()
    solved
  }

  def mkUnstableValue(v: V) = top

  private def substitute(pending: Pending[K, V], id: K, value: V): Result[K, V] = {

    val sum = pending.delta.map { prod =>
      if (prod.ids(id)) Component(value & prod.v, prod.ids - id) else prod
    }
    normalize(sum)
  }

  private def normalize(sum: SoP[K, V]): Result[K, V] = {
    var acc = bot
    var computableNow = true
    for (Component(v, prod) <- sum )
      if (prod.isEmpty || v == bot) acc = acc | v
      else computableNow = false

    if (acc == top || computableNow) Final(acc)
    else Pending(sum)
  }

}

class NullableResultSolver[K <: StableAwareId[K], V](doNothing: Boolean)(implicit lattice: Lattice[V])
  extends Solver[K, V](doNothing)(lattice) {
  override def mkUnstableValue(v: V) = bot
}
