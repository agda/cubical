{-# OPTIONS --cubical --safe --no-import-sorts #-}

module Cubical.Algebra.CommAlgebra.FinitelyPresented where
open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.GeneratedIdeal
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra

private
  variable
    ℓ : Level

module _ (R : CommRing {ℓ}) where
  free : (n : ℕ) → CommAlgebra R
  free n = R [ Lift (Fin n) ]

  
