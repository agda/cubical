{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.FGIdeal where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec

open import Cubical.Algebra.CommRing
import Cubical.Algebra.CommRing.FGIdeal as CRing
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Ideal

private
  variable
    ℓ ℓ' : Level
    R : CommRing ℓ

generatedIdeal : {n : ℕ} (A : CommAlgebra R ℓ') → FinVec ⟨ A ⟩ₐ n → IdealsIn R A
generatedIdeal A = CRing.generatedIdeal (CommAlgebra→CommRing A)

incInIdeal :   {n : ℕ} (A : CommAlgebra R ℓ')
              (U : FinVec ⟨ A ⟩ₐ n) (i : Fin n) → U i ∈ fst (generatedIdeal A U)
incInIdeal A = CRing.indInIdeal (CommAlgebra→CommRing A)

syntax generatedIdeal A V = ⟨ V ⟩[ A ]

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ') where
  open CommRingStr (A .fst .snd)

  opaque
    0FGIdeal≡0Ideal : {n : ℕ} → ⟨ replicateFinVec n 0r ⟩[ A ] ≡ (0Ideal R A)
    0FGIdeal≡0Ideal = CRing.0FGIdeal (CommAlgebra→CommRing A)

    inclOfFGIdeal : {n : ℕ} (V : FinVec ⟨ A ⟩ₐ n) (I : IdealsIn R A)
        → (∀ i → V i ∈ fst I) → fst ⟨ V ⟩[ A ] ⊆ fst I
    inclOfFGIdeal V I ∀i→Vi∈I = CRing.inclOfFGIdeal (CommAlgebra→CommRing A) V I ∀i→Vi∈I
