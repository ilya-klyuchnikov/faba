# FABA = Fast Bytecode Analysis

## Inference

    runMain faba.Main /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar results/jdk
    runMain faba.Main /Users/lambdamix/code/kanva-micro/data/commons-lang3-3.3.2.jar results/commons
    runMain faba.Main data/groovy-2.3.3.jar results/groovy.jar


## Precise Dependency Analysis

    runMain faba.experimental.Statistics --dirs /Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/ /Users/lambdamix/code/jetbrains/community/lib/
