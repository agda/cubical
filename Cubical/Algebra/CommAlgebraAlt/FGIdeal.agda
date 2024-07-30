{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebraAlt.FGIdeal where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal using ()
            renaming (generatedIdeal to generatedIdealCommRing;
                      indInIdeal to ringIncInIdeal;
                      0FGIdeal to 0FGIdealCommRing)
open import Cubical.Algebra.CommAlgebraAlt.Base
open import Cubical.Algebra.CommAlgebraAlt.Ideal

private
  variable
    ℓ : Level
    R : CommRing ℓ

generatedIdeal : {n : ℕ} (A : CommAlgebra R ℓ) → FinVec ⟨ A ⟩ₐ n → IdealsIn R A
generatedIdeal A = generatedIdealCommRing (CommAlgebra→CommRing A)

incInIdeal :   {n : ℕ} (A : CommAlgebra R ℓ)
              (U : FinVec ⟨ A ⟩ₐ n) (i : Fin n) → U i ∈ fst (generatedIdeal A U)
incInIdeal A = ringIncInIdeal (CommAlgebra→CommRing A)

syntax generatedIdeal A V = ⟨ V ⟩[ A ]

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) where
  open CommRingStr (A .fst .snd)

  0FGIdeal : {n : ℕ} → ⟨ replicateFinVec n 0r ⟩[ A ] ≡ (0Ideal R A)
  0FGIdeal = 0FGIdealCommRing (CommAlgebra→CommRing A)
