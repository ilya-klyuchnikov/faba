# Correctness of folding

Folding is performed if a current configuration is an instance of a previously encountered configuration. 

It may be surprising that folding is performed by taking into account only configurations.
Constraints are totally ignored.

The key consideration: constraints are monotone. It means that current constraints will be always 
more restricting than constraints from history. So, condition that current state is a more particular 
instance of a previous state holds here. 
