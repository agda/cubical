module Cubical.HITs.Truncation.FromNegTwo.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusOne
open import Cubical.HITs.Nullification
open import Cubical.HITs.Sn.Base

-- For the hub-and-spoke construction discussed in the HoTT book, which doesn't work in the base case
--  of contractibility, see `HITs.Truncation.Base`. The definition of truncation here contains
--  two more constructors which are redundant when n ≥ 1 but give contractibility when n = 0.

-- data hLevelTrunc {ℓ} (n : HLevel) (A : Type ℓ) : Type (ℓ-max ℓ ℓ') where
--   -- the hub-and-spoke definition in `Truncation.Base`
--   ∣_∣ : A → hLevelTrunc n A
--   hub   : (f : S (-1+ n) → hLevelTrunc n A) → hLevelTrunc n A
--   spoke : (f : S (-1+ n) → hLevelTrunc n A) (s : S) → hub f ≡ f s
--   -- two additional constructors needed to ensure that hLevelTrunc 0 A is contractible
--   ≡hub   : ∀ {x y} (p : S (-1+ n) → x ≡ y) → x ≡ y
--   ≡spoke : ∀ {x y} (p : S (-1+ n) → x ≡ y) (s : S (-1+ n)) → ≡hub p ≡ p s

hLevelTrunc : ∀ {ℓ} → HLevel → Type ℓ → Type ℓ
hLevelTrunc n A = Null {A = Unit} (λ _ → S (-1+ n)) A

-- Note that relative to the HoTT book, this notation is off by +2
∥_∥_ : ∀ {ℓ} → Type ℓ → HLevel → Type ℓ
∥ A ∥ n = hLevelTrunc n A
