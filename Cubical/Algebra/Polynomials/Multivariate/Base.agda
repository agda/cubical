module Cubical.Algebra.Polynomials.Multivariate.Base where

open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly public

{-

The Multivariate Polynomials of size n over a CommRing A is a CommRing.
This version is define as an instance of the more general constructions of gradedRing.
This done by defing Poly A n = ⊕HIT_{Vec A n} A where ⊕HIT is the HIT direct sum.
Then raising the _·_ to Poly A n.

See :
-}

open import Cubical.Algebra.GradedRing.DirectSumHIT

{-

This is define very shortly as a CommRing Instances calling a general makeGradedRing functions.
And by proving the additional properties that the _·_ is commutative.
Hence the absence of real Base and Properties files.

Some more properties that are comming from the definition using the ⊕HIT
can be found in the DirectSumHIT file such as eliminator.

-}

open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
