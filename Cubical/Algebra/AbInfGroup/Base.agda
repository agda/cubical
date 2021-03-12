{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.AbInfGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat

open import Cubical.Homotopy.Connected renaming (isConnected to isConnectedWrongLevel)
open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ : Level

isConnected : (n : ℕ) → Type ℓ → Type ℓ
isConnected n = isConnectedWrongLevel (suc (suc n))

leftCompPath : {A B C : Pointed ℓ} → A ≡ B → (B →∙ C) → (A →∙ C)
leftCompPath p f = f ∘∙ pathToPointedMap p

rightCompPath : {A B C : Pointed ℓ} → A →∙ B → B ≡ C → (A →∙ C)
rightCompPath f p = pathToPointedMap p ∘∙ f

record AbInfGroup (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor abInfGroup
  field
    delooping : ℕ → Pointed ℓ
    connected : (n : ℕ) → isConnected (suc n) (fst (delooping n))
    isDelooping : (n : ℕ) → Ω (delooping (suc n)) ≡ delooping n

record AbInfHom (A B : AbInfGroup ℓ) : Type ℓ where
  open AbInfGroup
  field
    map : (n : ℕ) → delooping A n →∙ delooping B n
    isDelooping : (n : ℕ) → leftCompPath (isDelooping A n) (map n)
                           ≡ rightCompPath (Ω→ (map (suc n))) (isDelooping B n)

{-
              map (n+1)

        Ω Bⁿ⁺¹ A →∙ Ω Bⁿ⁺¹ B
          ↓            ↓      isDelooping n
         Bⁿ A   →∙   Bⁿ B

               map n
-}
