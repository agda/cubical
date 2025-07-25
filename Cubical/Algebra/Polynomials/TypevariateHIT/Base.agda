module Cubical.Algebra.Polynomials.TypevariateHIT.Base where

{-
Typevariate polynomials over a commutative ring
===============================================

For a univariate polynomial, the type of variables is the unit type, for multivariate
polynomials it is a standard finite type. For a typevariate polynomial, the type of variables
is an arbitrary type I : Type. Since the CommRing R[I] is 0-truncated, the polynomials only depend
on the 0-truncation of I.
The typevariate polynomials are constructed as a free commutative algebra on the given I : Type.
They are justified by a proof of the universal property of a free commutative algebra.
-}

open import Cubical.Algebra.CommAlgebra.Polynomials public
