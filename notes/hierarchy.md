# Inference of annotations with hierarchy

See comments in `data.InferenceWithHierarchyData` about `INVOKEINTERFACE`, `INVOKEVIRTUAL`, `INVOKESPECIAL` and `INVOKESTATIC` instructions.

Soundness: a property of overridable method holds if it holds for __all__ possible methods during virtual calls.

2 cases:
  - non-abstract overridable method
  - abstract overridable method
Technical problem: not to fall into infinite recursion.

Things to do:
  - for non-stable calls - collect all hierarchy ()

Possible implementation strategy to do it step-by-step:
  1. Apply this logic without transitivity
  2. With transitivity

__The problem__: how to calculate dependencies?
- Equations are solved from bottom to top, but full resolution (all possible calls) happens in two directions: from top to bottom (`INVOKEINTERFACE`, `INVOKEVIRTUAL`) and from bottom to top (`INVOKESPECIAL`, `INVOKEVIRTUAL`).

__The solution__: one more stage of analysis.

The solution works correctly in a closed world. All implementations are here.

- The first stage: collecting equations.
  - Collecting analysis equations with delayed binding of call (context),
    just directly saving in equations information about call site -
    `INVOKEINTERFACE`, `INVOKEVIRTUAL`, `INVOKESPECIAL` or `INVOKESTATIC`.
  - Collecting hierarchy information: class relations and methods in this class/interface.
- The second stage: resolve call sites.
  - For all calls in `Pending` rhs resolve `Stage1` key to a set of `Stage2` keys (a lot of boilerplate):
    - `INVOKESPECIAL` - lookup of a method in the hierarchy from bottom to top, result is a single method. Get the hierarchy path
    - `INVOKESTATIC` - lookup of a method in the hierarchy from bottom to top, result is a single method.
    - `INVOKEVIRTUAL` - collect all concrete (non-abstract) inheritors of this class and resolve a method for them (in bottom-up manner).
    - `INVOKEINTERFACE` - the same as `INVOKEVIRTUAL`.
- The third stage: substitute all resolved sites as stable KEY.

__Technical issue__: How to substitute the result of resolve?

- Simplest technical solution: two level equations.
  - Each call has a quantifier: `SPECIAL`, `STATIC`, `INTERFACE`, `VIRTUAL`.
  - For each encountered quantifier an equation in the following form is created: `foo_SPECIAL = x1 | x2 | x3`.
  - Each LHS `key` is considered as `stable`.

#### Implementation.

- Class/interface - hierarchy.
- Class/interface - methods.
- In the first iteration, resolve may be done lazy - just by direct lookup.
- Collect/resolve/substitute should be performed for each namespace separately,
  since when resolve fails (no concrete methods)
