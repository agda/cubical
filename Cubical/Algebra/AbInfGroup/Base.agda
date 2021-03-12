{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.AbInfGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat

open import Cubical.Homotopy.Connected renaming (isConnected to isConnectedWrongLevel)
open import Cubical.Homotopy.Loopspace
open import Cubical.Algebra.AbGroup

private
  variable
    ℓ : Level

isConnected : (n : ℕ) → Type ℓ → Type ℓ
isConnected n = isConnectedWrongLevel (suc (suc n))

record AbInfGroup (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor abInfGroup
  field
    delooping : ℕ → Pointed ℓ
    connected : (n : ℕ) → isConnected (suc n) (fst (delooping n))
    isDelooping : (n : ℕ) → Ω (delooping (suc n)) ≃∙ delooping n

record AbInfHom (A B : AbInfGroup ℓ) : Type ℓ where
  open AbInfGroup
  field
    map : (n : ℕ) → delooping A n →∙ delooping B n
    isDelooping : (n : ℕ) →
      map n ∘∙ (≃∙To→∙ (isDelooping A n)) ≡ (≃∙To→∙ (isDelooping B n)) ∘∙ Ω→ (map (suc n))


{-
              map (n+1)

        Ω Bⁿ⁺¹ A →∙ Ω Bⁿ⁺¹ B
          ↓            ↓      isDelooping n
         Bⁿ A   →∙   Bⁿ B

               map n
-}
