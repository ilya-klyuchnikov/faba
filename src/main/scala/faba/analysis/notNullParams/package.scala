package faba.analysis

package object notNullParams {
  type CNF = Set[Set[Parameter]]

  implicit class CnfOps(val cnf1: CNF) {
    def join(cnf2: CNF): CNF =
      for {disj1 <- cnf1; disj2 <- cnf2} yield disj1 ++ disj2

    def meet(cnf2: CNF): CNF =
      cnf1 ++ cnf2
  }
}
