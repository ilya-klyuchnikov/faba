# Related work

* <http://findbugs.sourceforge.net/> - FindBugs performs analysis of bytecode. It infers `@NotNull` parameters under the hood (however, this inference is not such powerful as ours).

# Some links

* <http://www.sable.mcgill.ca/soot/>
* <http://homepages.ecs.vuw.ac.nz/~djp/JACK/> - java annotations checker
* <http://homepages.ecs.vuw.ac.nz/~djp/bml/> - it includes utilities for data flow analysis
* <http://javalib.gforge.inria.fr/Nit.html> - nullability inferrer, it has semantics different from KAnnotator: it answer the question which values are possible at a given point.
* <http://wala.sourceforge.net/wiki/index.php/Main_Page> - T.J. Watson Libraries for Analysis (WALA), includes solvers
* <http://pp.ipd.kit.edu/projects/joana/>, <https://github.com/jgf/joana> - JOANA (Java Object-sensitive ANAlysis) - Information Flow Control Framework for Java
* <https://bitbucket.org/jastadd/jastaddj-nonnullinference> - it is a bit buggy
* <http://www.drgarbage.com/control-flow-graph-factory.html> - Control Flow Graph Factory is an Eclipse plugin which generates control flow graphs from java bytecode
* <http://plse.cs.washington.edu/daikon/> - Daikon invariants detector
* <http://www.eecs.ucf.edu/~leavens/JML//index.shtml> - JML, java modeling language
* <http://www.hpl.hp.com/downloads/crl/jtk/> - Java Programming Toolkit Source Release from HP
* <http://www.cs.umd.edu/projects/PL/jqual/> - Type qualifier inference for Java
* <https://www.cs.purdue.edu/homes/hosking/bloat/> - BLOAT 
The Bytecode-Level Optimizer and Analysis Tool
* <http://www.cs.ucla.edu/~todd/research/pub.php?id=toplas10>, <http://javacop.sourceforge.net/> - JavaCOP: Pluggable type system for Java
* <http://www.cs.ucla.edu/~todd/research/udte.html> - User-Defined Type Extensions
