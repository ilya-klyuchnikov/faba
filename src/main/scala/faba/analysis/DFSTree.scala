package faba.analysis

import scala.collection.immutable.HashSet

case class DFSTree(preOrder: Array[Int],
                   postOrder: Array[Int],
                   tree: Set[(Int, Int)],
                   forward: Set[(Int, Int)],
                   back: Set[(Int, Int)],
                   cross: Set[(Int, Int)],
                   loopEnters: Set[Int]) {

  def isDescendant(child: Int, parent: Int): Boolean =
    preOrder(parent) <= preOrder(child) && postOrder(child) <= postOrder(parent)

}

sealed trait Action
case class MarkScanned(node: Int) extends Action
case class ExamineEdge(from: Int, to: Int) extends Action

object DFSTree {
  type Edge = (Int, Int)

  def build(transitions: Array[List[Int]]): DFSTree = {
    var tree, forward, back, cross = HashSet[Edge]()
    // marked = entered
    val marked = new Array[Boolean](transitions.length)
    val scanned = new Array[Boolean](transitions.length)
    val preOrder = new Array[Int](transitions.length)
    val postOrder = new Array[Int](transitions.length)

    var entered = 0
    var completed = 0
    val stack = scala.collection.mutable.Stack[Action]()
    var loopEnters = HashSet[Int]()

    @inline
    def enter(n: Int): Unit = {
      entered += 1
      preOrder(n) = entered
      marked(n) = true
      stack.push(MarkScanned(n))
      stack.pushAll(transitions(n).map(ExamineEdge(n, _)))
    }

    // entering
    enter(0)

    while (stack.nonEmpty) {
      val action = stack.pop()
      action match {
        case MarkScanned(n) =>
          completed += 1
          postOrder(n) = completed
          scanned(n) = true
        case ExamineEdge(from, to) =>
          if (!marked(to)) {
            enter(to)
            tree = tree + (from -> to)
          } else if (preOrder(to) > preOrder(from)) {
            forward = forward + (from -> to)
          } else if (preOrder(to) < preOrder(from) && !scanned(to)) {
            back = back + (from -> to)
            loopEnters = loopEnters + to
          } else {
            cross = cross + (from -> to)
          }
      }
    }

    DFSTree(preOrder, postOrder, tree, forward, back, cross, loopEnters)
  }
}
