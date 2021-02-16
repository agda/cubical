{-
  Finitely presented algebras.
  An R-algebra A is finitely presented, if there merely is an exact sequence
  of R-modules:

    (a₁,⋯,aₘ) → R[X₁,⋯,Xₙ] → A → 0
-}
{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Cubical.Algebra.CommAlgebra.FPAlgebra where
open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal

private
  variable
    ℓ : Level

module _ (Ring@(R , str) : CommRing {ℓ}) where
  free : (n : ℕ) → CommAlgebra Ring
  free n = Ring [ Lift (Fin n) ]


