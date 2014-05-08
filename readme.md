# FABA = Fast Bytecode Analysis

## Development

Ad-hoc testing

    runMain faba.NotNullParametersProcessor /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar jdk-params.txt
    runMain faba.NotNullParametersProcessor /Users/lambdamix/code/kanva-micro/data/commons-lang3-3.3.2.jar commons-params.txt
    runMain faba.NullBooleanContractsProcessor /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar jdk-null-boolean-contracts.txt
    runMain faba.NullBooleanContractsProcessor /Users/lambdamix/code/kanva-micro/data/commons-lang3-3.3.2.jar commons-null-boolean-contracts.txt
    runMain faba.NotNullBooleanContractsProcessor /Users/lambdamix/code/kanva-micro/data/commons-lang3-3.3.2.jar commons-notnull-boolean-contracts.txt
    runMain faba.NotNullBooleanContractsProcessor /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar jdk-notnull-boolean-contracts.txt
    runMain faba.NullObjectContractsProcessor /Users/lambdamix/code/kanva-micro/data/commons-lang3-3.3.2.jar commons-null-object-contracts.txt
    runMain faba.NullObjectContractsProcessor /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar jdk-null-object-contracts.txt

## Idea integration

The simplest solution is to do via annotation key - serialization.
