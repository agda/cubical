{-# OPTIONS --safe #-}
module Cubical.Algebra.Module.Instances.FinMatrix where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Functions.FunExtEquiv using (funExt₂)

open import Cubical.Data.Nat using (ℕ)

open import Cubical.Algebra.Matrix
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Module

module _ {ℓ} (R : Ring ℓ) {m n : ℕ} where

  open module R' = RingStr (str R) renaming (_+_ to _+r_; -_ to -r_)
  open LeftModuleStr

  FinVecLeftModule : LeftModule R ℓ
  fst FinVecLeftModule = FinMatrix ⟨ R ⟩ m n
  0m  (snd FinVecLeftModule) = λ _ _       → 0r
  _+_ (snd FinVecLeftModule) = λ xs ys x y → xs x y +r ys x y
  -_  (snd FinVecLeftModule) = λ xs x y    → -r xs x y
  _⋆_ (snd FinVecLeftModule) = λ r xs x y  → r · xs x y
  isLeftModule (snd FinVecLeftModule)    = isLeftModuleR
    where
    isLeftModuleR : IsLeftModule R _ _ _ _
    isLeftModuleR = makeIsLeftModule
      (isSetΠ2 λ _ _ → R'.is-set)
      (λ _ _ _ → funExt₂ λ _ _ → R'.+Assoc _ _ _)
      (λ _     → funExt₂ λ _ _ → R'.+IdR _)
      (λ _     → funExt₂ λ _ _ → R'.+InvR _)
      (λ _ _   → funExt₂ λ _ _ → R'.+Comm _ _)
      (λ _ _ _ → funExt₂ λ _ _ → sym (R'.·Assoc _ _ _))
      (λ _ _ _ → funExt₂ λ _ _ → ·DistR+ _ _ _)
      (λ _ _ _ → funExt₂ λ _ _ → ·DistL+ _ _ _)
      (λ _     → funExt₂ λ _ _ → R'.·IdL _)
