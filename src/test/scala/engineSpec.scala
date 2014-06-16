package faba.test

import org.scalatest.prop.TableDrivenPropertyChecks
import org.scalatest.FunSuite

import faba.engine._
import faba.data._

class engineSpec extends FunSuite with TableDrivenPropertyChecks {

  case class Utils[Id, Val:Lattice]() {
    val top = implicitly[Lattice[Val]].top
    val bot = implicitly[Lattice[Val]].bot

    def substitute(rhs: Result[Id, Val], solution: Map[Id, Val]): Val = rhs match {
      case Final(value) =>
        value
      case Pending(partial, sop) =>
        sop.map(_.ids.map(solution).reduce(_ & _)).reduce(_ | _)
    }

    implicit class SolutionOps(solution: Map[Id, Val]) {
      def validFor_?(equations: List[Equation[Id, Val]]): Boolean =
        equations.forall { case Equation(lhs, rhs) => solution(lhs) == substitute(rhs, solution)}
    }

    implicit class IdOps(i: Id) {
      def :=(v: Val): Equation[Id, Val] =
        Equation(i, Final(v))
      def :=(s: Set[Set[Id]]): Equation[Id, Val] =
        Equation(i, Pending(bot, s.map(Component(false, _))))
      def :=(s: Set[Id])(implicit x: String = null): Equation[Id, Val] =
        Equation(i, Pending(bot, Set(Component(false, s))))
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
      case Final(v) =>
        s"${eq.id} := $v;"
      case Pending(v, sop) =>
        s"${eq.id} := $v | ${sop.map(_.ids.mkString("(", " & ", ")")).mkString(" | ")};"
    }

  }

  case class Wrapper(s: Symbol) extends StableAwareId[Wrapper] {
    override val stable: Boolean = true
    override def mkStable: Wrapper = this
    override def mkUnstable: Wrapper = this
  }

  type Id = Wrapper
  implicit val lattice = ELattice(Values.Bot, Values.Top)
  val valuesUtils = Utils[Id, Values.Value]()
  import Values._
  import valuesUtils._

  implicit class SymbolOps(s: Symbol) {
    def i = Wrapper(s)
  }

  test("Modeling @NotNull parameters equations") {

    val equationSets =
      Table(
        "Equations",
        List(
          'a.i := NotNull,
          'b.i := I('a.i)
        ),
        List(
          'a.i := NotNull,
          'b.i := Top,
          'c.i := I('a.i) U I('b.i)
        ),
        List(
          'a.i := NotNull,
          'b.i := Top,
          'c.i := I('a.i) U I('a.i, 'b.i)
        )
      )

    forAll(equationSets) { equations =>
      val solution = new Solver(equations).solve()
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
          'a.i := True,
          'b.i := I('a.i)
        ),
        List(
          'a.i := True,
          'b.i := False,
          'c.i := I('a.i) U I('b.i)
        ),
        List(
          'a.i := True,
          'b.i := Top,
          'c.i := I('a.i) U I('a.i, 'b.i)
        ),
        List(
          'a.i := Top,
          'b.i := True,
          'c.i := I('a.i) U I('a.i, 'b.i)
        )
      )

    forAll(equationSets) { equations =>
      val solution = new Solver(equations).solve()
      info(s"equations: ${equations.map(pretty).mkString(" ")}")
      info(s"solution : ${solution}")
      assert(solution validFor_? equations, "invalid solution")
    }
  }

}
