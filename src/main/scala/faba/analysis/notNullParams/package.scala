package faba.analysis

import faba.analysis.engine.ELattice

package object notNullParams {
  // sum of products
  type DNF = Set[Set[Parameter]]

  implicit class CnfOps(val cnf1: DNF) {
    def join(cnf2: DNF): DNF =
      cnf1 ++ cnf2

    def meet(cnf2: DNF): DNF =
      for {disj1 <- cnf1; disj2 <- cnf2} yield disj1 ++ disj2
  }

  object Nullity extends Enumeration {
    val NotNull, Nullable = Value
  }
  implicit val nullityLattice = ELattice(Nullity)

  type Id = Parameter
  type Value = Nullity.Value
}
