module Cubical.Algebra.Module.Instances.FinVec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP using (str; ⟨_⟩)

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Module

module _ {ℓ} (R : Ring ℓ) {n : ℕ} where

  private open module R' = RingStr (str R) renaming (_+_ to _+r_; -_ to -r_)
  open LeftModuleStr

  FinVecLeftModule : LeftModule R ℓ
  fst FinVecLeftModule = FinVec ⟨ R ⟩ n
  0m  (snd FinVecLeftModule) = λ _       → 0r
  _+_ (snd FinVecLeftModule) = λ xs ys z → xs z +r ys z
  -_  (snd FinVecLeftModule) = λ xs z    → -r xs z
  _⋆_ (snd FinVecLeftModule) = λ r xs z  → r · xs z
  isLeftModule (snd FinVecLeftModule)    = isLeftModuleR
    where
    isLeftModuleR : IsLeftModule R _ _ _ _
    isLeftModuleR = makeIsLeftModule
      (isSet→ R'.is-set)
      (λ _ _ _ → funExt λ _ → R'.+Assoc _ _ _)
      (λ _     → funExt λ _ → R'.+IdR _)
      (λ _     → funExt λ _ → R'.+InvR _)
      (λ _ _   → funExt λ _ → R'.+Comm _ _)
      (λ _ _ _ → funExt λ _ → sym (R'.·Assoc _ _ _))
      (λ _ _ _ → funExt λ _ → ·DistR+ _ _ _)
      (λ _ _ _ → funExt λ _ → ·DistL+ _ _ _)
      (λ _     → funExt λ _ → R'.·IdL _)
