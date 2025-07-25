module Cubical.Algebra.Polynomials.UnivariateFun.Base where

open import Cubical.Algebra.CommRing.Polynomials.UnivariatePolyFun public

{-

The Univariate Functional Polynomials over a CommRing A is a CommRing.
The base type is define using almost null sequences ie functions.
This definition enables to defined a direct sum indexed by ℕ.
Thus base type and the AbGroup part of the CommRing is define an instance
of the more general Direct Sum one which can be found here :
-}

open import Cubical.Algebra.DirectSum.DirectSumFun.Base

{-

On this definition of the Direct Sum, it is possible to raise a Graded Ring structure.
Then complete it to be a CommRing. Those version of the polynomials are hence
a instance of this graded ring structure.

see : for the details of the constructions

-}

open import Cubical.Algebra.GradedRing.DirectSumFun
