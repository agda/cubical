{-

A simpler definition of truncation ∥ A ∥ n from n ≥ -1

Note that this uses the HoTT book's indexing, so it will be off
 from `∥_∥_` in HITs.Truncation.Base by -2

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.Truncation.Base where

open import Cubical.Data.NatMinusOne
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.Sn.Base
open import Cubical.Data.Nat.Base
open import Cubical.Data.Unit.Base
open import Cubical.Data.Empty

-- this definition is off by one. Use hLevelTrunc or ∥_∥ for truncations
-- (off by 2 w.r.t. the HoTT-book)
data HubAndSpoke {ℓ} (A : Type ℓ) (n : ℕ) : Type ℓ where
  ∣_∣ : A → HubAndSpoke A n
  hub : (f : S₊ n → HubAndSpoke A n) → HubAndSpoke A n
  spoke : (f : S₊ n → HubAndSpoke A n) (x : S₊ n) → hub f ≡ f x

hLevelTrunc : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Type ℓ
hLevelTrunc zero A = Unit*
hLevelTrunc (suc n) A = HubAndSpoke A n

∥_∥_ : ∀ {ℓ} (A : Type ℓ) (n : ℕ) → Type ℓ
∥ A ∥ n = hLevelTrunc n A

∣_∣ₕ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → A → ∥ A ∥ n
∣_∣ₕ {n = zero} a = tt*
∣_∣ₕ {n = suc n} a = ∣ a ∣
