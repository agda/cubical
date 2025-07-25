module Cubical.Algebra.Module.Instances.FinMatrix where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP using (str; ⟨_⟩)

open import Cubical.Functions.FunExtEquiv using (funExt₂)

open import Cubical.Data.Nat using (ℕ)

open import Cubical.Algebra.Matrix
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Module

open import Cubical.Algebra.Module.Instances.FinVec

module _ {ℓ} (R : Ring ℓ) {m n : ℕ} where

  private
    open module R' = RingStr (str R) renaming (_+_ to _+r_; -_ to -r_)
    module FV {n} = LeftModuleStr (str (FinVecLeftModule R {n}))
  open LeftModuleStr

  FinMatrixLeftModule : LeftModule R ℓ
  fst FinMatrixLeftModule = FinMatrix ⟨ R ⟩ m n
  0m  (snd FinMatrixLeftModule) = λ _       → FV.0m
  _+_ (snd FinMatrixLeftModule) = λ xs ys x → xs x FV.+ ys x
  -_  (snd FinMatrixLeftModule) = λ xs x    → FV.- xs x
  _⋆_ (snd FinMatrixLeftModule) = λ r xs x  → r FV.⋆ xs x
  isLeftModule (snd FinMatrixLeftModule)    = isRLeftModule
    where
    isRLeftModule : IsLeftModule R _ _ _ _
    isRLeftModule = makeIsLeftModule
      (isSetΠ λ _ → FV.is-set)
      (λ _ _ _ → funExt₂ λ _ _ → R'.+Assoc _ _ _)
      (λ _     → funExt₂ λ _ _ → R'.+IdR _)
      (λ _     → funExt₂ λ _ _ → R'.+InvR _)
      (λ _ _   → funExt₂ λ _ _ → R'.+Comm _ _)
      (λ _ _ _ → funExt₂ λ _ _ → sym (R'.·Assoc _ _ _))
      (λ _ _ _ → funExt₂ λ _ _ → ·DistR+ _ _ _)
      (λ _ _ _ → funExt₂ λ _ _ → ·DistL+ _ _ _)
      (λ _     → funExt₂ λ _ _ → R'.·IdL _)
