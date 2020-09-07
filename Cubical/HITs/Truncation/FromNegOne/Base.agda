{-

An simpler definition of truncation ∥ A ∥ n from n ≥ -1

Note that this uses the HoTT book's indexing, so it will be off
 from `∥_∥_` in HITs.Truncation.Base by -2

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Truncation.FromNegOne.Base where

open import Cubical.Data.NatMinusOne renaming (suc₋₁ to suc)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.Sn
open import Cubical.Data.Nat.Base renaming (suc to sucℕ)
open import Cubical.Data.Unit.Base

data  ∥_∥⁻¹_ {ℓ} (A : Type ℓ) (n : ℕ₋₁) : Type ℓ where
  ∣_∣ : A  → ∥ A ∥⁻¹ n
  hub : (f : S (suc n) → ∥ A ∥⁻¹ n) → ∥ A ∥⁻¹ n
  spoke : (f : S (suc n) → ∥ A ∥⁻¹ n) (x : S (suc n)) → hub f ≡ f x

hLevelTrunc : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Type ℓ
hLevelTrunc zero A = Unit*
hLevelTrunc (sucℕ n) A = ∥ A ∥⁻¹ (-1+ n)

∥_∥_ : ∀ {ℓ} (A : Type ℓ) (n : ℕ) → Type ℓ
∥ A ∥ n = hLevelTrunc n A
