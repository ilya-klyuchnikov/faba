# FABA = Fast Bytecode Analysis

## FAQ

* __What is FABA about?__ 
    * It infers `@Nullable`, `@NotNull`, `@Contract` annotations for java libraries
* __Do I need source code of a library?__
    * No, FABA inspects bytecode only.
* __What is the output__?
    * XML files in the format of Intellij IDEA external annotations. <https://www.jetbrains.com/idea/webhelp/external-annotations.html>.
* __Is it for production?__
    * No.
* __What is for then?__
    * FABA is a research playground for testing and prototyping new ideas and algorithms of bytecode analysis implemented in Intellij IDEA.
    * In other words, FABA to some extent is a reference implementation of Intellij IDEA bytecode analysis.
* __What is Intellij IDEA bytecode analysis?__
    * <http://blog.jetbrains.com/idea/2014/10/automatic-notnullnullablecontract-inference-in-intellij-idea-14/>
* __Is Intellij IDEA bytecode analysis open source?__
    * Yes. <https://github.com/JetBrains/intellij-community/tree/master/java/java-analysis-impl/src/com/intellij/codeInspection/bytecodeAnalysis>

## How to run

    faba.Main path_to_lib1.jar path_to_lib2.jar output dir 
    
It is easier to experiment with FABA directly from sbt:

    runMain faba.Main /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar results/jdk
    runMain faba.Main /Users/lambdamix/code/kanva-micro/data/commons-lang3-3.3.2.jar results/commons
    runMain faba.Main data/groovy-2.3.3.jar results/groovy.jar
