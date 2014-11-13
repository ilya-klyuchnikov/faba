package faba.engine

import faba.data.{LimitReachedException, PolymorphicId}

import scala.collection.mutable

object `package` {

  /**
   * The central data of FABA. Equation represents a staged result of analysis.
   *
   * @param id left hand side of the equation (variable)
   * @param rhs right hand side of the equation: answer (faba.engine.Final) or expression (faba.engine.Pending)
   * @tparam K type of identifiers (variables, keys)
   * @tparam V type of values (answers)
   */
  case class Equation[K, V](id: K, rhs: Result[K, V])

  /**
   * Canonical representations of "lattice expressions".
   * In a sense, it is disjunctive normal form (http://en.wikipedia.org/wiki/Disjunctive_normal_form)
   * == OR of ANDs == sum of products == JOIN of MEETs.
   * Solver is designed to work with such expressions
   *
   * @tparam K type of identifiers (variables, keys)
   * @tparam V type of values (answers)
   * @see [[faba.engine.Pending#expression]]
   */
  type SumOfProducts[K, V] = Set[Product[K, V]]

  /**
   * Product (meet) of lattice elements (= AND = MEET)
   *
   * @param upperBound the upper bound of product, used by solver during applying substitutions
   * @param elems elements of this product
   * @tparam K type of identifiers (variables, keys)
   * @tparam V type of values (answers)
   */
  case class Product[K, V](upperBound: V, elems: Set[K])

  /**
   * Right hand side of an equation
   * @tparam K type of identifiers (variables, keys)
   * @tparam V type of values (answers)
   */
  sealed trait Result[+K, V]

  /**
   * "Answer", solution
   * @param value solution per se
   * @tparam V type of values (answers)
   */
  case class Final[V](value: V) extends Result[Nothing, V]

  /**
   * Right hand side of an equation, not a final answer.
   *
   * @param expression expression per se
   * @tparam K type of identifiers (variables, keys)
   * @tparam V type of values (answers)
   */
  case class Pending[K, V](expression: SumOfProducts[K, V]) extends Result[K, V] {
    if (expression.map(_.elems.size).sum > 30) throw new LimitReachedException
  }

  /**
   * Utility to join results. Used by ResultAnalysis to combined partials solutions.
   * @param l lattice
   * @tparam K type of identifiers (variables, keys)
   * @tparam V type of values (answers)
   */
  case class ResultUtils[K, V](l: Lattice[V]) {
    val top: V = l.top
    def join(r1: Result[K, V], r2: Result[K, V]): Result[K, V] = (r1, r2) match {
      case (Final(`top`), _) =>
        Final(`top`)
      case (_, Final(`top`)) =>
        Final(`top`)
      case (Final(v1), Final(v2)) =>
        Final(l.join(v1, v2))
      case (Final(v1), Pending(comps2)) =>
        Pending(comps2 + Product(v1, Set()))
      case (Pending(comps1), Final(v2)) =>
        Pending(comps1 + Product(v2, Set()))
      case (Pending(comps1), Pending(comps2)) =>
        Pending(comps1 union comps2)
    }
  }
}

/**
 * Lattice for values. All equations are over lattices with `meet` and `join` operations.
 *
 * @param bot bottom of the lattice (lower bound)
 * @param top top of the lattice (upper bound)
 * @tparam V type of values in the lattice
 */
case class Lattice[V](bot: V, top: V) {

  /**
   * Join operation (http://en.wikipedia.org/wiki/Join_and_meet)
   */
  final def join(x: V, y: V): V =
    (x, y) match {
      case (`bot`, _) => y
      case (_, `bot`) => x
      case (`top`, _) => top
      case (_, `top`) => top
      case _ => if (equiv(x, y)) x else top
    }

  /**
   * Meet operation (http://en.wikipedia.org/wiki/Join_and_meet)
   */
  final def meet(x: V, y: V): V =
    (x, y) match {
      case (`top`, _) => y
      case (_, `top`) => x
      case (`bot`, _) => bot
      case (_, `bot`) => bot
      case _ => if (equiv(x, y)) x else bot
    }

  /**
   * equivalence = equality here
   */
  final def equiv(x: V, y: V): Boolean =
    x == y
}

/**
 * Solver of equations over lattices. Solving is performed simply by substitution.
 *
 * @param idleMode solver in idle mode does nothing
 * @param lattice lattice to use for solving (bot, top, meet, join)
 * @tparam K type of identifiers (variables, keys)
 * @tparam V type of values in the lattice
 */
class Solver[K <: PolymorphicId[K], V](val idleMode: Boolean, val lattice: Lattice[V]) {

  type Solution = (K, V)
  import lattice._

  private val dependencies = mutable.HashMap[K, Set[K]]()
  private val pending = mutable.HashMap[K, Pending[K, V]]()
  private val moving = mutable.Queue[Solution]()
  private var solved = Map[K, V]()

  // for testing
  def this(equations: List[Equation[K, V]], lattice: Lattice[V]) {
    this(false, lattice)
    equations.foreach(addEquation)
  }

  def addEquation(equation: Equation[K, V]): Unit =
    if (!idleMode) equation.rhs match {
      case Final(value) =>
        moving enqueue (equation.id -> value)
      case Pending(sum) => normalize(sum) match {
        case Final(value) =>
          moving enqueue (equation.id -> value)
        case p@Pending(comps) =>
          for (trigger <- comps.map(_.elems).flatten) {
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

    pending.clear()
    solved
  }

  def mkUnstableValue(v: V) = top

  private def substitute(pending: Pending[K, V], id: K, value: V): Result[K, V] = {

    val sum = pending.expression.map { prod =>
      if (prod.elems(id)) Product(meet(value, prod.upperBound), prod.elems - id) else prod
    }
    normalize(sum)
  }

  private def normalize(sum: SumOfProducts[K, V]): Result[K, V] = {
    var acc = bot
    var computableNow = true
    for (Product(v, prod) <- sum )
      if (prod.isEmpty || v == bot) acc = join(acc, v)
      else computableNow = false

    if (acc == top || computableNow) Final(acc)
    else Pending(sum)
  }

}

class NullableResultSolver[K <: PolymorphicId[K], V](idle: Boolean, lattice: Lattice[V])
  extends Solver[K, V](idle, lattice) {
  override def mkUnstableValue(v: V) = lattice.bot
}
