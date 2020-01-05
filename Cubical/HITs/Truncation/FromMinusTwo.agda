{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.FromMinusTwo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusTwo
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation renaming (∥_∥ to ∥_∥₋₁) hiding (∣_∣)
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.GroupoidTruncation
open import Cubical.HITs.2GroupoidTruncation

import Cubical.HITs.Truncation.Base as FromMinusOne
import Cubical.HITs.Truncation.Properties as FromMinusOne

∥_∥_ : ∀ {ℓ} (A : Type ℓ) (n : ℕ₋₂) → Type ℓ
∥ A ∥ neg2  = Lift Unit
∥ A ∥ suc n = FromMinusOne.∥ A ∥ (1+ n)

∣_∣ : ∀ {ℓ} {A : Type ℓ} {n : ℕ₋₂} → A → ∥ A ∥ n
∣_∣ {n = neg2} = λ _ → lift tt
∣_∣ {n = suc n} = FromMinusOne.∣_∣

isOfHLevel∥∥ : ∀ {ℓ} {A : Type ℓ} (n : ℕ₋₂) → isOfHLevel (2+ n) (∥ A ∥ n)
isOfHLevel∥∥ neg2    = lift tt , λ { (lift tt) → refl }
isOfHLevel∥∥ (suc n) = FromMinusOne.isOfHLevel∥∥ (1+ n)

propTrunc≃Trunc-1 : ∀ {ℓ} {A : Type ℓ} → ∥ A ∥₋₁ ≃ ∥ A ∥ -1
propTrunc≃Trunc-1 = FromMinusOne.propTrunc≃Trunc-1

setTrunc≃Trunc0 : ∀ {ℓ} {A : Type ℓ} → ∥ A ∥₀ ≃ ∥ A ∥ 0
setTrunc≃Trunc0 = FromMinusOne.setTrunc≃Trunc0

groupoidTrunc≃Trunc1 : ∀ {ℓ} {A : Type ℓ} → ∥ A ∥₁ ≃ ∥ A ∥ 1
groupoidTrunc≃Trunc1 = FromMinusOne.groupoidTrunc≃Trunc1

2groupoidTrunc≃Trunc2 : ∀ {ℓ} {A : Type ℓ} → ∥ A ∥₂ ≃ ∥ A ∥ 2
2groupoidTrunc≃Trunc2 = FromMinusOne.2groupoidTrunc≃Trunc2
