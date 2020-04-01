{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.Nullary.DecidableEq where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    A : Type ℓ
-- Proof of Hedberg's theorem: a type with decidable equality is an h-set

Dec→Stable : (A : Type ℓ) → Dec A → Stable A
Dec→Stable A (yes x) = λ _ → x
Dec→Stable A (no x) = λ f → ⊥.elim (f x)

-- Hedberg's theorem
Discrete→isSet : ∀ {ℓ} {A : Type ℓ} → Discrete A → isSet A
Discrete→isSet d = Stable≡→isSet (λ x y → Dec→Stable (x ≡ y) (d x y))
