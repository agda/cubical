{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.FGIdeal where
open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal using ()
            renaming (generatedIdeal to generatedIdealCommRing;
                      0FGIdeal to 0FGIdealCommRing)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal

private
  variable
    ℓ : Level
    R : CommRing ℓ

generatedIdeal : {n : ℕ} (A : CommAlgebra R ℓ) → FinVec (fst A) n → IdealsIn A
generatedIdeal A = generatedIdealCommRing (CommAlgebra→CommRing A)

syntax generatedIdeal A V = ⟨ V ⟩[ A ]

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) where
  open CommAlgebraStr (snd A)
  private
    ⟨_⟩ : {n : ℕ} → FinVec (fst A) n → IdealsIn A
    ⟨ V ⟩ = ⟨ V ⟩[ A ]

  0FGIdeal : {n : ℕ} → ⟨ replicateFinVec n 0a ⟩ ≡ (0Ideal A)
  0FGIdeal = 0FGIdealCommRing (CommAlgebra→CommRing A)
