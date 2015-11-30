## New algorithm

All objects/data are divided into:

- `this` - `this` field
- `local` - data, created inside the method. Like `Object x = new Object();`
- `parameter#n` - passed parameter.
- `owned` - fields for each we know that they are known by current object (escape analysis?)
- `unknown`

All effects are represented via union types. 
The method has `unknown` (`top`) effect, or has effects represented via the sum of the following small effects:

- `TOP`
- `THIS_CHANGE` - changes the state of the object
- `PARAM#N_CHANGE` - changes the state of the parameter (writes to a parameter).
- `PURE` - pure method

### The inference (inference rules)

1. Data analysis - all data are divided into `this`, `local`, `parameter#n`, `unknown` via standard analysis.
2. For each instructions we define its effect. The effect of a method is the sum of all effects of instructions.

We are interested only in the following instructions:

- `PUTFIELD`
- `PUTSTATIC`
- `IASTORE`, `LASTORE`, `FASTORE`, `DASTORE`, `AASTORE`, `BASTORE`, `CASTORE`, `SASTORE`
- `INVOKEDYNAMIC`, `INVOKEINTERFACE`, `INVOKEVIRTUAL`, `INVOKESPECIAL`, `INVOKESTATIC`

All other instructions are not interesting for us at all!

- `PUTFIELD`
    - `this.x=...`        => `THIS_CHANGE`
    - `owned.x=...`       => `THIS_CHANGE`
    - `local.x=...`       => `PURE`
    - `parameter#n.x=...` => `PARAM#N_CHANGE`
    - `other.x=...`       => `TOP`
- `PUTSTATIC`
    - `x.x=...`           => `TOP`
- `_STORE`
    - `owned[i]=...`      => `THIS_CHANGE`
    - `local[i]=...`      => `PURE`
    - `parameter#n`       => `PARAM#N_CHANGE`
    - `unknown[i]=...`    => `TOP`
- `invoke` - The most interesting case cause `invoke` can have a set of effects
    - pattern matching is performed for `invoke` first (each of effects of invoke) and then for data
    - `TOP` => `TOP`
    - `PURE` => `PURE`
    - `THIS_CHANGE` (analysis by receiver)
        - `THIS` => `THIS_CHANGE`
        - `local` => `PURE`
        - `parameter#n` => `PARAM#N_CHANGE`
        - `owned` => `THIS_CHANGE`
        - `unknown` => `TOP`
    - `PARAM#N_CHANGE` (analysis by nth-argument)
        - `this` => `THIS_CHANGE`
        - `local` => `PURE`
        - `parameter#n` => `PARAM#N_CHANGE`
        - `owned` => `THIS_CHANGE`
        - `unknown` => `TOP`
        
### Indexing

1. Data analysis
2. Instructions analysis - first, analyzing `PUTFIELD`, `PUTSTATIC`, `_STORE`, then - `invoke`

For each `invoke` instruction we need to store receiver and arguments. That's it.

### Todo

For final classes we can "devirtualize" virtual calls to `this`.
Also we can consider "hard-coded closed hierarchies" - like `AbstractStringBuilder`, `StringBuilder`, `StringBuffer`.
Other problems are with hierarchy.

What can we do? - Apply the same logic?

The solution: option to resolve inheritance.
