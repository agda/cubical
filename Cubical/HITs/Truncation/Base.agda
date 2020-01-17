{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.NatMinusOne using (ℕ₋₁; neg1; suc)
open import Cubical.Data.NatMinusTwo
open import Cubical.HITs.Sn

open import Cubical.Data.Unit

open import Cubical.Foundations.Embedding
open import Cubical.Foundations.Isomorphism

-- for ∥ A ∥ -2 we use a notion of 'pointed sphere' in the spoke constructor

S∙ : ℕ₋₁ → Type₀
S∙ neg1    = Unit
S∙ (suc n) = S (suc n)

apS∙ : ∀ {ℓ} {A : Type ℓ} {n} → (S∙ n → A) → S n → A
apS∙ {n = neg1 } f ()
apS∙ {n = suc _} f = f

data  ∥_∥_ {ℓ} (A : Type ℓ) (n : ℕ₋₂) : Type ℓ where
  ∣_∣ : A  → ∥ A ∥ n
  hub : (f : S (1+ n) → ∥ A ∥ n) → ∥ A ∥ n
  spoke : (f : S∙ (1+ n) → ∥ A ∥ n) (s : S∙ (1+ n)) → hub (apS∙ f) ≡ f s
