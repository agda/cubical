{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.AbInfGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Structures.Pointed using (pointedSIP)

open import Cubical.Homotopy.Connected renaming (isConnected to isConnectedWrongLevel)
open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ : Level

isConnected : (n : ℕ) → Type ℓ → Type ℓ
isConnected n = isConnectedWrongLevel (suc (suc n))

private
  eqToPointedMap : {A B : Pointed ℓ} → A ≡ B → (A →∙ B)
  eqToPointedMap {A = A} {B = B} p = {!invEquiv (pointedSIP A B)!}

leftCompEq : {A B C : Pointed ℓ} → A ≡ B → (B →∙ C) → (A →∙ C)
leftCompEq p f = {!!} , {!!}

record AbInfGroup (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor abInfGroup
  field
    delooping : ℕ → Pointed ℓ
    connected : (n : ℕ) → isConnected (suc n) (fst (delooping n))
    isDelooping : (n : ℕ) → Ω (delooping (suc n)) ≡ delooping n
{-
record AbInfHom (A B : AbInfGroup ℓ) : Type ℓ where
  open AbInfGroup
  field
    map : (n : ℕ) → delooping A n →∙ delooping B n
    isDelooping : (n : ℕ) → (Ω→ (map (suc n))) ≡ map n
-}
