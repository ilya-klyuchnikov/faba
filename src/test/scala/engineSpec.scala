package faba.test

import org.scalatest.prop.TableDrivenPropertyChecks
import org.scalatest.FunSuite

import faba.engine._
import faba.data._

class engineSpec extends FunSuite with TableDrivenPropertyChecks {

  case class Utils[K, V:Lattice]() {
    val lattice = implicitly[Lattice[V]]
    val top = implicitly[Lattice[V]].top
    val bot = implicitly[Lattice[V]].bot

    def substitute(rhs: Result[K, V], solution: Map[K, V]): V = rhs match {
      case Final(value) =>
        value
      case Pending(sop) =>
        sop.map(_.elems.map(solution).reduce(lattice.meet)).reduce(lattice.join)
    }

    implicit class SolutionOps(solution: Map[K, V]) {
      def validFor_?(equations: List[Equation[K, V]]): Boolean =
        equations.forall { case Equation(lhs, rhs) => solution(lhs) == substitute(rhs, solution)}
    }

    implicit class IdOps(i: K) {
      def :=(v: V): Equation[K, V] =
        Equation(i, Final(v))
      def :=(s: Set[Set[K]]): Equation[K, V] =
        Equation(i, Pending(s.map(Product(top, _))))
      def :=(s: Set[K])(implicit x: String = null): Equation[K, V] =
        Equation(i, Pending(Set(Product(top, s))))
    }

    implicit class IdSetOps(s: Set[K]) {
      // union
      def U(i: Set[K]): Set[Set[K]] = Set(s, i)
    }

    implicit class IdSetSetOps(s: Set[Set[K]]) {
      // union
      def U(t: Set[K]): Set[Set[K]] = s + t
    }

    // intersection
    def I(ids: K*): Set[K] = Set(ids:_*)

    def pretty(eq: Equation[K, V]): String = eq.rhs match {
      case Final(v) =>
        s"${eq.id} := $v;"
      case Pending(sop) =>
        s"${eq.id} := ${sop.map(_.elems.mkString("(", " & ", ")")).mkString(" | ")};"
    }

  }

  case class Wrapper(s: Symbol) extends PolymorphicId[Wrapper] {
    override val stable: Boolean = true
    override def mkStable: Wrapper = this
    override def mkUnstable: Wrapper = this
  }

  type Id = Wrapper
  implicit val lattice = Lattice(Values.Bot, Values.Top)
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
      val solution = new Solver(equations, lattice).solve()
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
      val solution = new Solver(equations, lattice).solve()
      info(s"equations: ${equations.map(pretty).mkString(" ")}")
      info(s"solution : ${solution}")
      assert(solution validFor_? equations, "invalid solution")
    }
  }

}
