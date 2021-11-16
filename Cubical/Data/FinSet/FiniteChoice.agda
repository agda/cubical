{-

Axiom of Finite Choice

Yep, it's a theorem actually.

-}
{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.FiniteChoice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation renaming (rec to TruncRec ; elim to TruncElim)

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Data.SumFin renaming (Fin to SumFin)
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties

private
  variable
    ℓ ℓ' ℓ'' : Level

choice≃SumFin :
    {n : ℕ}(Y : SumFin n → Type ℓ) → ((x : SumFin n) → ∥ Y x ∥) ≃ ∥ ((x : SumFin n) → Y x) ∥
choice≃SumFin {n = 0} Y =
    isContr→≃Unit (isContrΠ⊥)
  ⋆ Unit≃Unit*
  ⋆ invEquiv (propTruncIdempotent≃ isPropUnit*)
  ⋆ propTrunc≃ (invEquiv (isContr→≃Unit* (isContrΠ⊥ {A = Y})))
choice≃SumFin {n = suc n} Y =
    Π⊎≃
  ⋆ Σ-cong-equiv-fst (ΠUnit (λ x → ∥ Y (inl x) ∥))
  ⋆ Σ-cong-equiv-snd (λ _ → choice≃SumFin {n = n} (λ x → Y (inr x)))
  ⋆ Σ-cong-equiv-fst (propTrunc≃ (invEquiv (ΠUnit (λ x → Y (inl x)))))
  ⋆ ∥∥-×-≃
  ⋆ propTrunc≃ (invEquiv (Π⊎≃ {E = Y}))

module _
  (X : Type ℓ)(p : ≃Fin X)
  (Y : X → Type ℓ') where

  private
    q = ≃Fin→SumFin p
    e = q .snd

  choice≃' : ((x : X) → ∥ Y x ∥) ≃ ∥ ((x : X) → Y x) ∥
  choice≃' =
      equivΠ {B' = λ x → ∥ Y (invEq e x) ∥} e (transpFamily q)
    ⋆ choice≃SumFin _
    ⋆ propTrunc≃ (invEquiv (equivΠ {B' = λ x → Y (invEq e x)} e (transpFamily q)))

module _
  ((X , p) : FinSet ℓ)
  (Y : X → Type ℓ') where

  choice≃ : ((x : X) → ∥ Y x ∥) ≃ ∥ ((x : X) → Y x) ∥
  choice≃ =
    TruncRec
      (isOfHLevel≃ 1 (isPropΠ (λ x → isPropPropTrunc)) (isPropPropTrunc))
      (λ p → choice≃' X p Y) p

  choice : ((x : X) → ∥ Y x ∥) → ∥ ((x : X) → Y x) ∥
  choice = choice≃ .fst
