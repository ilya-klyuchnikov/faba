package faba.analysis.nullBooleanContracts

import scala.collection.mutable
import scala.collection.immutable.HashSet
import scala.collection.mutable.ArrayBuffer
import faba.analysis.core.engine.Lattice

case class Equation(parameter: Parameter, solution: Dependence)
case class Dependence(partial: Option[Value], params: Set[Parameter])

sealed trait Value
case object Top extends Value
case object True extends Value
case object False extends Value
case object Null extends Value
case object NotNull extends Value
case object Bot extends Value

object ValuesLattice extends Lattice[Value] {
  override val top: Value = Top
  override val bot: Value = Bot
}

// all contracts are the same!
class Solver {

  val dependencies =
    mutable.HashMap[Parameter, HashSet[Parameter]]()

  val solved =
    ArrayBuffer[Equation]()
  val toPropagate =
    mutable.Queue[Equation]()
  val pending =
    mutable.HashMap[Parameter, Equation]()

  var count = 0

  def addEquation(equation: Equation): Unit = {
    equation.solution match {
      case Dependence(Some(Top), _) =>
        toPropagate.enqueue(equation)
      case Dependence(Some(_), params) if params.isEmpty =>
        toPropagate.enqueue(equation)
      case Dependence(_, params) =>
        val parameter = equation.parameter
        for (trigger <- params) {
          dependencies(trigger) = dependencies.getOrElse(trigger, HashSet()) + parameter
        }
        pending(equation.parameter) = equation
    }
  }

  def solve(): Unit = {

    while (toPropagate.nonEmpty) {
      val equation = toPropagate.dequeue()

      val param = equation.parameter
      val dParams = dependencies.remove(param).getOrElse(Set[Parameter]())

      equation.solution match {
        // propagate Top - all dependent contracts become Top as well
        case Dependence(Some(Top), s) if s.isEmpty =>
          for {
            dParam <- dParams
            Equation(_, Dependence(_, _)) <- pending.remove(dParam)
          } {
            toPropagate.enqueue(Equation(dParam, Dependence(Some(Top), Set())))
          }

        // propagate a solution, the propagated solution should matched against partial solution
        // otherwise -> top
        case Dependence(Some(comp), s) if s.isEmpty =>
          solved += equation
          for {
            dParam <- dParams
            Equation(_, Dependence(pSol, params)) <- pending.remove(dParam)
          } {
            val params1 = params - param
            val comp1: Option[Value] = pSol match {
              case None => Some(comp)
              case Some(`comp`) => Some(comp)
              case _ => Some(Top)
            }

            if (comp1 == Some(Top)) {
              toPropagate.enqueue(Equation(dParam, Dependence(Some(Top), Set())))
            } else if (params1.isEmpty) {
              toPropagate.enqueue(Equation(dParam, Dependence(comp1, Set())))
            } else {
              pending(dParam) = Equation(dParam, Dependence(comp1, params1))
            }
          }
      }
    }
  }

}
