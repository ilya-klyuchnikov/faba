# FABA = Fast Bytecode Analysis

## Quick Start

Infer `@NotNull` annotations for `jarFile` and write result to `outFile`

    $ sbt
    > runMain faba.NotNullParametersProcessor jarFile outFile

Example run:

    $ sbt
    > runMain faba.NotNullParametersProcessor /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar out.txt

Infer `@Contact(_, null, _) -> false`, `@Contact(_, null, _) -> true` annotations and write result to `outFile`

    $ sbt
    > runMain faba.NullBooleanContractsProcessor jarFile outFile

Example run:

    $ sbt
    > runMain faba.NullBooleanContractsProcessor /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar out.txt

## Development

Ad-hoc testing

    runMain faba.NotNullParametersProcessor /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar jdk-params.txt
    runMain faba.NotNullParametersProcessor /Users/lambdamix/code/kanva-micro/data/commons-lang3-3.3.2.jar commons-params.txt
    runMain faba.NullBooleanContractsProcessor /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar jdk-null-contracts.txt
    runMain faba.NullBooleanContractsProcessor /Users/lambdamix/code/kanva-micro/data/commons-lang3-3.3.2.jar commons-null-contracts.txt
    runMain faba.NotNullBooleanContractsProcessor /Users/lambdamix/code/kanva-micro/data/commons-lang3-3.3.2.jar commons-notnull-contracts.txt
    runMain faba.NotNullBooleanContractsProcessor /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar jdk-notnull-contracts.txt

## Idea integration

The simplest solution is to do via annotation key - serialization.
