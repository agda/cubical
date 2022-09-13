{-
  The generator 'X' of the algebra of univariate polynomials is a regular element,
  i.e. the multiplication map 'X ·_' is injective (we will actually show it is an Embedding)
-}
{-# OPTIONS --safe #-}

module Cubical.Algebra.CommAlgebra.FreeCommAlgebra.RegularGenerator where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Polynomials.UnivariateList.Properties

private variable
    ℓ : Level
