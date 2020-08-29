An attempt at ring solving
========================================

There is a need for a ring solver similar to this one:

https://github.com/oisdk/agda-ring-solver

It is explained in this thesis:

https://github.com/oisdk/agda-ring-solver-report/blob/master/report.pdf

It would be great to have the reflection interface and a minimal (not neccessarily fast) working version.

The thesis above refers to this paper:

"Proving Equalities in a Commutative Ring Done Right in Coq"
https://link.springer.com/content/pdf/10.1007%2F11541868_7.pdf

There are three parts of the appraoch to prove x=y:
* turn x and y into Expressions (i.e. syntax trees) using reflection
* map the expressions to polynomials in horner form (normalize)
* let agda compare the results with unification
