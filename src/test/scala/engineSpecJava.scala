package com.intellij.codeInspection.bytecodeAnalysis

import scala.collection.JavaConversions._

import org.scalatest.prop.TableDrivenPropertyChecks
import org.scalatest.FunSuite

class engineSpecJava extends FunSuite with TableDrivenPropertyChecks {

  case class Utils[Id, Val<:Enum[Val]](lattice: ELattice[Val]) {
    val top = lattice.top
    val bot = lattice.bot

    def substitute(rhs: Result[Id, Val], solution: java.util.Map[Id, Val]): Val = rhs match {
      case f:Final[Id, Val] =>
        f.value
      case p:Pending[Id, Val] =>
        p.delta.map(_.ids.map(solution).reduce(lattice.meet)).reduce(lattice.join)
    }

    implicit class SolutionOps(solution: java.util.Map[Id, Val]) {
      def validFor_?(equations: List[Equation[Id, Val]]): Boolean =
        equations.forall { eq => solution(eq.id) == substitute(eq.rhs, solution)}
    }

    implicit class IdOps(i: Id) {
      def :=(v: Val): Equation[Id, Val] =
        new Equation(i, new Final(v))
      def :=(s: Set[Set[Id]]): Equation[Id, Val] =
        new Equation(i, new Pending(bot, s.map(new Component(false, _))))
      def :=(s: Set[Id])(implicit x: String = null): Equation[Id, Val] =
        new Equation(i, new Pending(bot, Set(new Component(false, s))))
    }

    implicit class IdSetOps(s: Set[Id]) {
      // union
      def U(i: Set[Id]): Set[Set[Id]] = Set(s, i)
    }

    implicit class IdSetSetOps(s: Set[Set[Id]]) {
      // union
      def U(t: Set[Id]): Set[Set[Id]] = s + t
    }

    // intersection
    def I(ids: Id*): Set[Id] = Set(ids:_*)

    def pretty(eq: Equation[Id, Val]): String = eq.rhs match {
      case f:Final[_, _] =>
        s"${eq.id} := ${f.value};"
      case p:Pending[_, _] =>
        s"${eq.id} := ${p.infinum} | ${p.delta.map(_.ids.mkString("(", " & ", ")")).mkString(" | ")};"
    }

  }

  type Id = Symbol


  implicit val valueLattice = new ELattice(Value.Bot, Value.Top)
  val valueUtils = Utils[Id, Value](valueLattice)

  import Value._
  import valueUtils._


  test("Modeling @NotNull parameters equations") {

    val equationSets =
      Table(
        "Equations",
        List(
          'a := NotNull,
          'b := I('a)
        ),
        List(
          'a := NotNull,
          'b := Top,
          'c := I('a) U I('b)
        ),
        List(
          'a := NotNull,
          'b := Top,
          'c := I('a) U I('a, 'b)
        )
      )

    forAll(equationSets) { equations =>
      val solution = new Solver(valueLattice, equations).solve()
      info(s"equations: ${equations.map(pretty).mkString(" ")}")
      info(s"solution : ${solution}")
      assert(solution validFor_? equations, "invalid solution")
    }
  }

  test("Modeling contract equations") {

    val equationSets =
      Table(

        "Equations",

        List(
          'a := True,
          'b := I('a)
        ),
        List(
          'a := True,
          'b := False,
          'c := I('a) U I('b)
        ),
        List(
          'a := True,
          'b := Top,
          'c := I('a) U I('a, 'b)
        ),
        List(
          'a := Top,
          'b := True,
          'c := I('a) U I('a, 'b)
        )
      )


    forAll(equationSets) { equations =>
      val solution = new Solver(valueLattice, equations).solve()
      info(s"equations: ${equations.map(pretty).mkString(" ")}")
      info(s"solution : ${solution}")
      assert(solution validFor_? equations, "invalid solution")
    }
  }

}
