# FABA = Fast Bytecode Analysis

## Development

Ad-hoc testing

    runMain faba.NotNullParametersProcessor /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar jdk-params.txt
    runMain faba.NotNullParametersProcessor /Users/lambdamix/code/kanva-micro/data/commons-lang3-3.3.2.jar commons-params.txt
    runMain faba.InOutProcessor /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar jdk
    runMain faba.InOutProcessor /Users/lambdamix/code/kanva-micro/data/commons-lang3-3.3.2.jar commons


## Idea integration

The simplest solution is to do via annotation key - serialization.
