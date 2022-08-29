{-# OPTIONS --safe #-}
module Cubical.Algebra.Polynomials.UnivariateHIT.Base where

open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyHIT public

{-

The Univariate Functional Polynomials over a CommRing A are a CommRing.
The base type is defined using a HIT.
This definition enables us to define a direct sum indexed by ℕ.
Thus base type and the AbGroup part of the CommRing is defined as an instance
of the more general Direct Sum which can be found here:

-}

open import Cubical.Algebra.DirectSum.DirectSumHIT.Base

{-

On this definition of the Direct Sum, it is possible to define a Graded Ring structure.
Then complete it to be a CommRing. Those version of the polynomials are hence
an instance of this graded ring structure.

Follow the import below, for the details of the constructions:

-}

open import Cubical.Algebra.GradedRing.DirectSumHIT
