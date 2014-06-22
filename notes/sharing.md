# Smart sharing

In Faba the result of processing of each configuration is memoized.
You may try to minimize the number of memoized configurations for performance reasons.
The intricate point is that you can't say in advance (using some control-flow analysis) which configurations should be memoized and which should not.

One of my naive attempts to minimize memoization was to use DFS tree and memoize only configurations that correspond to "multi-entrance" instructions in DFS tree.
(Multi-entrance instruction have more that one incoming edge).
It was naive - you can't optimize in this way.
Consider the following control-flow graph.


      a
     / \
    b   c
     \ /
      d
      |
      e
      |
      f

Naive analysis says that only `d` is a "multi-entrance" instruction. However, the following tricky situation is possible:

        a(1)
        / \
       /   \
      /     \
    b(2)   c(3)
     |       |
    d(4)   d(5)
     |       |
    e(6)   e(6)

Configurations in `d` (4 and 5) are different. But their child configurations at `e` instructions are the same.
    
