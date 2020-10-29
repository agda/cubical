{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.Sigma where


import Agda.Primitive.Cubical

open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat renaming (elim to ℕ-elim)
open import Cubical.Data.Nat.Order

open import Cubical.Data.Vec
open import Cubical.Data.Fin renaming (elim to Fin-elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum 

open import Cubical.HITs.Interval
open import Cubical.HITs.PropositionalTruncation renaming (map to mapₚ)
open import Cubical.HITs.Sn
open import Cubical.HITs.S1 hiding (_*_)
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps
import Cubical.Functions.Logic as Lo

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.IntervalPrim

open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying
open import Cubical.Data.Sigma.Nested.Path

variable
  ℓ : Level


iso-NCube : ∀ {n} → ∀ {A : Type ℓ}  
              → Iso
                (NCube (suc n) → A)
                ((Σ[ x₀ ∈ (NCube n → A) ] Σ[ x₁ ∈ (NCube n → A) ] x₀ ≡ x₁))

(Iso.fun (iso-NCube {n = n}) x) = _ , (_ , (λ i → x i∷ i))
Iso.inv (iso-NCube {n = n}) (_ , _ , snd₁) (x ∷ x₁) = Iapp= snd₁ x x₁
Iso.rightInv (iso-NCube {n = n}) b = refl

Iso.leftInv (iso-NCube {n = n}) a i (end false ∷ x₁) =  a (end false ∷ x₁)
Iso.leftInv (iso-NCube {n = n}) a i (end true ∷ x₁) = a (end true ∷ x₁)
Iso.leftInv (iso-NCube {n = n}) a i (inside i₁ ∷ x₁) = a (inside i₁ ∷ x₁)



IsoCub : {A : Type ℓ} → ∀ n → Iso (NCube n → A ) (Cubeⁿ n A)

Iso.fun (IsoCub 0) x = x []
Iso.inv (IsoCub 0) x _ = x
Iso.rightInv (IsoCub 0) b = refl
Iso.leftInv (IsoCub 0) a i [] = a []

IsoCub {A = A} (suc n) =
      _ Iso⟨ iso-NCube  ⟩
      _ Iso⟨ equivToIso
              (cong≃ (λ T → (Σ[ x₀ ∈ T ] Σ[ x₁ ∈ T ] x₀ ≡ x₁)) (isoToEquiv (IsoCub {A = A} n)))  ⟩
      _ Iso⟨ invIso (nestedΣᵣ-combine-iso λ _ → NCubeSig' n A) ⟩ _ ∎Iso


-- ≃Border : {A : Type ℓ} → ∀ n →
--                (Σ[ x₀ ∈  (Cubeⁿ n A)] Σ[ x₁ ∈ (Cubeⁿ n A) ]
--                      Σ[ cyl ∈ cubeBd n A x₀ ≡ cubeBd n A x₁ ]
--                            PathP (λ i → InsideOfⁿ' {n = n} {A = A} (cyl i))
--                                 (cubeIns n A x₀) (cubeIns n A x₁))
--                               ≃
--                         (Boundaryⁿ' (suc n) A)
-- ≃Border = {!!}
