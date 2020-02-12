{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.NatMinusOne using (ℕ₋₁; neg1; suc)
open import Cubical.Data.NatMinusTwo
open import Cubical.HITs.Nullification
open import Cubical.HITs.Sn

-- For the hub-and-spoke construction discussed in the HoTT book, which only works for n ≥ -1, see
--  `HITs.Truncation.FromNegOne`. The definition of truncation here contains two more constructors
--  which are redundant when n ≥ -1 but give contractibility when n = -2.

-- data ∥_∥_ {ℓ} (A : Type ℓ) (n : ℕ₋₂) : Type (ℓ-max ℓ ℓ') where
--   -- the hub-and-spoke definition in `Truncation.FromNegOne`
--   ∣_∣ : A → Null S A
--   hub   : (f : S (1+ n) → ∥ A ∥ n) → ∥ A ∥ n
--   spoke : (f : S (1+ n) → ∥ A ∥ n) (s : S) → hub f ≡ f s
--   -- two additional constructors needed to ensure that ∥ A ∥ -2 is contractible
--   ≡hub   : ∀ {x y} (p : S (1+ n) → x ≡ y) → x ≡ y
--   ≡spoke : ∀ {x y} (p : S (1+ n) → x ≡ y) (s : S) → ≡hub p ≡ p s

∥_∥_ : ∀ {ℓ} → Type ℓ → ℕ₋₂ → Type ℓ
∥ A ∥ n = Null (S (1+ n)) A

