{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Truncation.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusOne
open import Cubical.Data.NatMinusTwo hiding (-1+_)
open import Cubical.HITs.Nullification
open import Cubical.HITs.Sn

-- For the hub-and-spoke construction discussed in the HoTT book, which doesn't work in the base case
--  of contractibility, see `HITs.Truncation.FromNegOne`. The definition of truncation here contains
--  two more constructors which are redundant when n ≥ 1 but give contractibility when n = 0.

-- data hLevelTrunc {ℓ} (n : ℕ) (A : Type ℓ) : Type (ℓ-max ℓ ℓ') where
--   -- the hub-and-spoke definition in `Truncation.FromNegOne`
--   ∣_∣ : A → hLevelTrunc n A
--   hub   : (f : S (-1+ n) → hLevelTrunc n A) → hLevelTrunc n A
--   spoke : (f : S (-1+ n) → hLevelTrunc n A) (s : S) → hub f ≡ f s
--   -- two additional constructors needed to ensure that hLevelTrunc 0 A is contractible
--   ≡hub   : ∀ {x y} (p : S (-1+ n) → x ≡ y) → x ≡ y
--   ≡spoke : ∀ {x y} (p : S (-1+ n) → x ≡ y) (s : S (-1+ n)) → ≡hub p ≡ p s

hLevelTrunc : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
hLevelTrunc n A = Null (S (-1+ n)) A

-- a re-indexing of `hLevelTrunc` which is consistent with the HoTT book
∥_∥_ : ∀ {ℓ} → Type ℓ → ℕ₋₂ → Type ℓ
∥ A ∥ n = hLevelTrunc (2+ n) A -- ≡ Null (S (1+ n)) A
