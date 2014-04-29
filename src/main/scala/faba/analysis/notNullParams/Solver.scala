package faba.analysis.notNullParams

import scala.collection.mutable
import scala.collection.immutable.HashSet
import scala.collection.mutable.ArrayBuffer

case class Equation(parameter: Parameter, solution: Solution)

sealed trait Solution
case object Nullable extends Solution
case object NotNull extends Solution
case class Dependence(cnf: CNF) extends Solution

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
      case Nullable | NotNull =>
        toPropagate.enqueue(equation)
      case Dependence(cnf) =>
        val parameter = equation.parameter
        for (main <- cnf.flatten) {
          dependencies(main) = dependencies.getOrElse(main, HashSet()) + parameter
        }
        pending(equation.parameter) = equation
    }
    count += 1
  }

  def solve(): Unit = {
    while (toPropagate.nonEmpty) {
      val equation = toPropagate.dequeue()
      solved += equation
      val param = equation.parameter
      val dependent = dependencies.remove(param).getOrElse(Set[Parameter]())
      equation.solution match {
        // propagate NotNull: remove all disjunctions with this parameter,
        // if CNF empty, solution is @NotNull
        case NotNull =>
          for {
            dParam <- dependent
            Equation(_, Dependence(cnf)) <- pending.remove(dParam)
          } {
            val cnf1 = cnf.filterNot(_(param))
            if (cnf1.isEmpty) toPropagate.enqueue(Equation(dParam, NotNull))
            else pending(dParam) = Equation(dParam, Dependence(cnf1))
          }
        // propagate Nullable: remove a parameter from all disjunctions,
        // if there is an empty disjunction, solution is @Nullable
        case Nullable => for {
          dParam <- dependent
          Equation(_, Dependence(cnf)) <- pending.remove(dParam)
        } {
          val cnf1 = cnf.map(_ - param)
          if (cnf1.exists(_.isEmpty)) toPropagate.enqueue(Equation(dParam, Nullable))
          else pending(dParam) = Equation(dParam, Dependence(cnf1))
        }
        case _ =>

      }
    }
  }
}
