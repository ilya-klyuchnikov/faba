# FABA = Fast Bytecode Analysis

## FAQ

* __What is FABA about?__
    * It infers `@Nullable`, `@NotNull`, `@Contract` annotations for java libraries.
      And FABA is really __fast__: it processes JDK for ~30 sec.
* __Does FABA perform global analysis of libraries?__
    * Yes! FABA takes into account nested calls at infinite depth!
* __Why is FABA fast?__
    * See `FABA architecture` section below.
* __Do I need source code of a library?__
    * No, FABA inspects bytecode only.
* __What is the output__?
    * XML files in the format of IntelliJ IDEA external annotations.
      See <https://www.jetbrains.com/idea/webhelp/external-annotations.html>.
* __Is it for production?__
    * No.
* __What is for then?__
    * FABA is a research playground for testing and prototyping new ideas and
      algorithms of bytecode analysis implemented in IntelliJ IDEA.
    * In other words, FABA to some extent is a reference implementation of
      IntelliJ IDEA bytecode analysis.
* __What is IntelliJ IDEA bytecode analysis?__
    * <http://blog.jetbrains.com/idea/2014/10/automatic-notnullnullablecontract-inference-in-intellij-idea-14/>
* __Is IntelliJ IDEA bytecode analysis open source?__
    * Yes. <https://github.com/JetBrains/intellij-community/tree/master/java/java-analysis-impl/src/com/intellij/codeInspection/bytecodeAnalysis>
* __What is the difference between FABA and IDEA 14 inference?__
    * The top priority of IDEA analysis was the speed of analysis, so some
      features of inference were sacrificed to the speed of indexing in IDEA.
    * FABA version [`1.0`](https://github.com/ilya-klyuchnikov/faba/releases/tag/v1.0)
      corresponds to IDEA implementation.
    * More `@NotNull` annotations are inferred by current FABA
      (more aggressive propagation of `@NotNull` constraints).
    * Possibly, more powerful analysis will be ported to IDEA in the future.
    * Current FABA stores all equations in memory (see section `FABA architecture` below) and solves them at once.
      IDEA dumps equations to indices and solves these equations lazily.
      (IDEA's indices are too IDEA-specific to be reproduced here.)
* __What are next steps?__
    * `@Contract` inference performs a lot of unnecessary operations.
      Many contract are not intuitive (meaningless, to be honest).
      Like this one:
      `@Contract("!null,_,_,_->true;_,!null,_,_->;true;_,_,!null,_->true")`.
      Tuning contracts is a lot of technical boilerplate.
    * Taking hierarchy into account.
      A lot of research and experiments.
      It is likely that indexing and inference will be 2-3 times slower.
    * Deeper inference of purity.
      It requires an effect system under the hood (`@Pure`, `@Read`, `@Write`, `@LocalEffect`).
    * Handling nullity of fields (at least `static final` and `final`).
* __What is the license?__
    * [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0.html).

## How to run

    faba.Main path_to_lib1.jar path_to_lib2.jar output_dir

It is easier to experiment with FABA directly from sbt:

    runMain faba.Main /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar results/jdk
    runMain faba.Main /Users/lambdamix/code/kanva-micro/data/commons-lang3-3.3.2.jar results/commons
    runMain faba.Main data/groovy-2.3.3.jar results/groovy.jar

## FABA architecture

There are a few principles that make FABA fast, robust and scalable.

* __Staged global analysis__. Indexing, equations, solving.
  * Each method is processed (indexed) exactly once.
    The result of processing is an equation.
    Equations consume reasonable small amount of memory.
    Equations hold only necessary information needed for certain analysis.
    In some sense, a method's bytecode is supercompiled in an equation.
    Indexing of methods is fast.
  * When all methods are processed, all equations are solved together at once.
    Solving equations takes a few seconds even for a large set of libraries.
* __Specialized analyses and equations__.
  * Many small specialized indexers for each inference.
    * Separate analysis and a separate equation for inference of __each__ `@NotNull` parameter.
    * Separate analysis and a separate equation for inference of __each__ `@Nullable` parameter.
    * Separate analysis and a separate equation for inference of a `@NotNull` method.
    * Separate analysis and a separate equation for inference of a `@Nullable` method.
    * Separate analysis and a separate equation for inference of __each__ `_,null,_->...`, `_,!null,_->...` clause.
    * Separate analysis and a separate equation for inference of pure methods.
  * Supercompilation instead of classical dataflow analysis.
* __Fast auxiliary analyses__
  * Auxiliary analyses accelerates primary analyses.
    * Leaking parameters analysis.
    * Result origins analysis.
    * Parameter to result flow analysis.

## Quick FABA code documentation for hackers

The main parts of FABA are written in Scala and minor parts are written in Java.
FABA relies on [ASM framework](http://asm.ow2.org/) for bytecode reading and semantic based bytecode interpretation.
Some extensions and specialization of ASM are implemented in Java (via copy-patch technology).

### Java part

The minor parts of FABA (in alphabetical order).

- [/src/main/java/faba/asm](/src/main/java/faba/asm) - specialized and patched classes from `asm` lib
  - [`faba.asm.AnalyzerExt`](/src/main/java/faba/asm/AnalyzerExt.java)
    - Extended version of `org.objectweb.asm.tree.analysis.Analyzer`.
      It handles frames _and_ `Data`.
      Used in `NullableResultAnalysis`, `Data` is a set of constraints (dereferenced values) in this case.
  - [`faba.asm.FramelessAnalyzer`](/src/main/java/faba/asm/FramelessAnalyzer.java)
    - Specialized lite version of `org.objectweb.asm.tree.analysis.Analyzer`.
      Used to build control flow graph.
      Calculation of fix-point of frames is removed, since frames are not needed to build control flow graph.
      So, the main point here is handling of subroutines (`jsr`) and try-catch-finally blocks.
  - [`faba.asm.InterpreterExt`](/src/main/java/faba/asm/InterpreterExt.java)
    - Trait for an interpreter (to be mixed with `org.objectweb.asm.tree.analysis.Interpreter`) which calculates additional constraints.
      Used in `NullableResultAnalysis` to propagate information about not null values.
  - [`faba.asm.LiteAnalyzer`](/src/main/java/faba/asm/LiteAnalyzer.java)
    - Specialized lite version of `org.objectweb.asm.tree.analysis.Analyzer`.
      No processing of subroutines.
      May be used for methods without `JSR/RET` instructions.
  - [`faba.asm.LiteAnalyzerExt`](/src/main/java/faba/asm/LiteAnalyzerExt.java):
    - Fusion of `faba.asm.LiteAnalyzer` and `faba.asm.AnalyzerExt`.
  - [`faba.asm.LiteFramelessAnalyzer`](/src/main/java/faba/asm/LiteFramelessAnalyzer.java)
    - Fusion of `faba.asm.LiteAnalyzer` and `faba.asm.FramelessAnalyzer`
  - [`faba.asm.Subroutine`](/src/main/java/faba/asm/Subroutine.java)
    - Copy of `org.objectweb.asm.tree.analysis.Subroutine`.

### Scala part

The main parts of FABA, in logical (how to read) order, functionalities (classes, utilities) are grouped by file.

- [`/src/main/scala`](/src/main/scala) - directory (without subdirectories) contains main classes (common infrastructure and orchestration).
  - [`data.scala`](/src/main/scala/data.scala)
    - Data structures for representing result of analyses, utilities to serialize inferred annotations into xml.
  - [`engine.scala`](/src/main/scala/engine.scala)
    - Lattices, equations over lattices, fast solver of equations.
  - [`source.scala`](/src/main/scala/source.scala)
    - IO infrastructure to traverse java bytecode (jar-files, classes in folders, classes reachable from classloader)
  - [`faba.scala`](/src/main/scala/faba.scala)
    - The main logic of orchestration of different analysis.
      Runs different analyses and puts equations got from different analyzers into corresponding solvers.
      It corresponds to indexing of java libraries.
  - [`main.scala`](/src/main/scala/main.scala)
    - Solving of equations gathered at indexing phase, dumping of solutions in the form of external annotations into xml files.
- [`/src/main/scala/analysis`](/src/main/scala/analysis) - the heart of FABA, different analyses
  - [`core.scala`](/src/main/scala/analysis/core.scala)
    - Core data structures used for analyses:
      - control flow graph
      - DFS tree
      - abstract values for semantic interpretation
      - configuration
      - state (configuration + history + constraints)
      - `StagedScAnalysis` - Skeleton for implementing staged analysis via exploration of graph of configurations.
  - [`utils.scala`](/src/main/scala/analysis/utils.scala) - `AnalysisUtils`
    - Equivalence relations for configurations and states, "instance of" (subset) relation.
  - [`combined.scala`](/src/main/scala/analysis/combined.scala)
    - "All in one" staged analysis - for linear methods (without branching).
      All equations are constructed in a single pass over method's instructions.
      It is a good point to look at for understanding of mechanics of all analyses.
  - [`parameters.scala`](/src/main/scala/analysis/parameters.scala)
    - `NotNullParameterAnalysis` - construction of equations for inference of `@NotNull` parameters.
    - `NullableParameterAnalysis` - construction of equations for inference of `@Nullable` parameters.
  - [`result.scala`](/src/main/scala/analysis/result.scala)
    - `ResultAnalysis` - construction of equations for inference of `@NotNull` methods,
      construction of equations for inference of `@Contract("_,null,_->?")` contracts.
  - [`nullableResult.scala`](/src/main/scala/analysis/nullableResult.scala)
    - `NullableResultAnalysis` - inference of `@Nullable` methods.
      Analysis is not based on supercompilation (to be fast).
      Really, current `@Nullable` method analysis is quite ad hoc and may be better if rewritten to supercompilation approach.
  - [`controlFlow.scala`](/src/main/scala/analysis/controlFlow.scala)
    - Utilities to build control flow graph, depth-first search tree and testing reducibility of control flow graph.
      Construction of control flow graph is also specialized for methods without `JSR/RET` instructions.
  - [`leakingParameters.scala`](/src/main/scala/analysis/leakingParameters.scala)
    - `LeakingParameters` analysis.
      Sound approximation of parameters usage.
      Preliminary analysis to explore whether next `@NotNull` parameter analysis,
      `@Nullable` parameter analysis and `@Contract` analysis will produce interesting result.
      In many cases leaking parameter analysis allows to understand the result of more complex analysis in a fast manner.
      Another result of this analysis is a fixed point of frames states (it is used later for result origins analysis).
  - [`resultOrigins.scala`](/src/main/scala/analysis/resultOrigins.scala)
    - Analysis to understand at which instructions values that may become the result of the method are created.
      Result origins analysis speeds up `ResultAnalysis` a lot.
  - [`parameterToResultFlow.scala`](/src/main/scala/analysis/parameterToResultFlow.scala)
    - Analysis to understand whether a method may just return a given parameter.
  - [`purity.scala`](/src/main/scala/analysis/purity.scala)
    - Very simple (not deep) analysis to infer pure methods (`@Contract(pure=true)`).
