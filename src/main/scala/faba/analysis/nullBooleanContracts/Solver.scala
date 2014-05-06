package faba.analysis.nullBooleanContracts

import scala.collection.mutable
import scala.collection.immutable.HashSet
import scala.collection.mutable.ArrayBuffer

case class Equation(parameter: Parameter, solution: Dependence)
case class Dependence(partial: Option[PartialSolution], params: Set[Parameter])

sealed trait PartialSolution
case object TrueComponent extends PartialSolution
case object FalseComponent extends PartialSolution
case object AnyComponent extends PartialSolution

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
      case Dependence(Some(AnyComponent), _) =>
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
        // propagate Any - all dependent contracts become Unknown as well
        case Dependence(Some(AnyComponent), s) if s.isEmpty =>
          for {
            dParam <- dParams
            Equation(_, Dependence(_, _)) <- pending.remove(dParam)
          } {
            toPropagate.enqueue(Equation(dParam, Dependence(Some(AnyComponent), Set())))
          }
        // propagate a solution, the propagated solution should matched against partial solution
        case Dependence(Some(comp), s) if s.isEmpty =>
          solved += equation
          for {
            dParam <- dParams
            Equation(_, Dependence(pSol, params)) <- pending.remove(dParam)
          } {
            val params1 = params - param
            val comp1: Option[PartialSolution] = pSol match {
              case None => Some(comp)
              case Some(`comp`) => Some(comp)
              case _ => Some(AnyComponent)
            }
            if (comp1 == Some(AnyComponent)) {
              toPropagate.enqueue(Equation(dParam, Dependence(Some(AnyComponent), Set())))
            } else {
              toPropagate.enqueue(Equation(dParam, Dependence(comp1, params1)))
            }
          }
      }
    }

  }

}
