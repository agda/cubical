Ring solving
========================================

This is a ring solver similar to this one:

https://github.com/oisdk/agda-ring-solver

The latter is explained in this thesis:

https://github.com/oisdk/agda-ring-solver-report/blob/master/report.pdf

The thesis refers to this paper:

"Proving Equalities in a Commutative Ring Done Right in Coq"
https://link.springer.com/content/pdf/10.1007%2F11541868_7.pdf

There are three parts of the appraoch to prove x=y:
* turn x and y into Expressions (i.e. syntax trees) using reflection
* map the expressions to polynomials in horner form (normalize)
* let agda compare the results with unification

There are two versions of the solver, one which works for natural numbers and one which works for commutatitive rings (CommRing). Only the CommRingSolver has a reflection interface and the NatSolver has some additional problems, but it could still be useful.

To see how the ring solver might be used, check out 'Examples.agda'. To understand how it works, it is probably good to have a look at 'NatExamples.agda' and 'CommRingExamples.agda'.

