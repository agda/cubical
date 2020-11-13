Ring solving
========================================

This is a crude ring solver similar to this one:

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

So far, the ring solver here works kind of ok for the natural numbers,
but it fails sometimes for an abstract ring.
The ring solver here could need a nice reflection interface like oisdk's.

To understand how the ring solver works and it might be used, have a look at 'Examples.agda'.

