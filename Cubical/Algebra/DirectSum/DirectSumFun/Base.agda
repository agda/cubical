{-# OPTIONS --safe #-}
module Cubical.Algebra.DirectSum.DirectSumFun.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.AbGroup

private variable
  ℓ : Level

open AbGroupStr

-----------------------------------------------------------------------------
-- Definition

AlmostNull : (G : ℕ → Type ℓ) → (Gstr : (n : ℕ) → AbGroupStr (G n))
             → (f : (n : ℕ) → G n) → Type ℓ
AlmostNull G Gstr f = ∃[ m ∈ ℕ ] ((n : ℕ) → m < n → f n ≡ 0g (Gstr n))

⊕Fun : (G : ℕ → Type ℓ) → (Gstr : (n : ℕ) → AbGroupStr (G n)) → Type ℓ
⊕Fun G Gstr = Σ[ f ∈ ((n : ℕ) → G n) ] AlmostNull G Gstr f

isSet⊕Fun : (G : ℕ → Type ℓ) → (Gstr : (n : ℕ) → AbGroupStr (G n)) → isSet (⊕Fun G Gstr)
isSet⊕Fun G Gstr = isSetΣSndProp (isSetΠ (λ n → is-set (Gstr n))) (λ _ → squash₁)
