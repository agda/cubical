{-

Axiom of Finite Choice
- Yep, it's a theorem actually.

-}
{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.FiniteChoice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Data.SumFin
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties

private
  variable
    ℓ ℓ' : Level

choice≃Fin :
  {n : ℕ}(Y : Fin n → Type ℓ) → ((x : Fin n) → ∥ Y x ∥₁) ≃ ∥ ((x : Fin n) → Y x) ∥₁
choice≃Fin {n = 0} Y =
    isContr→≃Unit (isContrΠ⊥)
  ⋆ Unit≃Unit*
  ⋆ invEquiv (propTruncIdempotent≃ isPropUnit*)
  ⋆ propTrunc≃ (invEquiv (isContr→≃Unit* (isContrΠ⊥ {A = Y})))
choice≃Fin {n = suc n} Y =
    Π⊎≃
  ⋆ Σ-cong-equiv-fst (ΠUnit (λ x → ∥ Y (inl x) ∥₁))
  ⋆ Σ-cong-equiv-snd (λ _ → choice≃Fin {n = n} (λ x → Y (inr x)))
  ⋆ Σ-cong-equiv-fst (propTrunc≃ (invEquiv (ΠUnit (λ x → Y (inl x)))))
  ⋆ ∥∥-×-≃
  ⋆ propTrunc≃ (invEquiv (Π⊎≃ {E = Y}))

module _
  (X : Type ℓ)(p : isFinOrd X)
  (Y : X → Type ℓ') where

  private
    e = p .snd

  choice≃' : ((x : X) → ∥ Y x ∥₁) ≃ ∥ ((x : X) → Y x) ∥₁
  choice≃' =
      equivΠ {B' = λ x → ∥ Y (invEq e x) ∥₁} e (transpFamily p)
    ⋆ choice≃Fin _
    ⋆ propTrunc≃ (invEquiv (equivΠ {B' = λ x → Y (invEq e x)} e (transpFamily p)))

module _
  (X : FinSet ℓ)
  (Y : X .fst → Type ℓ') where

  choice≃ : ((x : X .fst) → ∥ Y x ∥₁) ≃ ∥ ((x : X .fst) → Y x) ∥₁
  choice≃ =
    Prop.rec
      (isOfHLevel≃ 1 (isPropΠ (λ x → isPropPropTrunc)) isPropPropTrunc)
      (λ p → choice≃' (X .fst) (_ , p) Y) (X .snd .snd)

  choice : ((x : X .fst) → ∥ Y x ∥₁) → ∥ ((x : X .fst) → Y x) ∥₁
  choice = choice≃ .fst
