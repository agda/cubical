{-# OPTIONS --safe #-}
module Cubical.Algebra.Module.Instances.VecFin where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData

open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Module

module _ {ℓ} (R : Ring ℓ) {n : ℕ} where

  open module R' = RingStr (snd R) renaming (_+_ to _+r_; -_ to -r_)
  open IsMonoid using (isSemigroup; ·IdR; ·IdL)
  open LeftModuleStr
  open IsLeftModule
  open IsSemigroup using (is-set; ·Assoc)
  open IsGroup using (isMonoid; ·InvR; ·InvL)
  open IsAbGroup

  private
    VRN = FinVec ⟨ R ⟩ n
    0r' : VRN
    0r' _ = 0r
    _+'_ : VRN → VRN → VRN
    (xs +' ys) z = xs z +r ys z
    -'_ : VRN → VRN
    (-' xs) z = -r xs z
    _⋆'_ : ⟨ R ⟩ → VRN → VRN
    (r ⋆' xs) z = r · xs z

  FinVecLeftModule : LeftModule R ℓ
  fst FinVecLeftModule = FinVec ⟨ R ⟩ n
  0m  (snd FinVecLeftModule) = 0r'
  _+_ (snd FinVecLeftModule) = _+'_
  -_  (snd FinVecLeftModule) = -'_
  _⋆_ (snd FinVecLeftModule) = _⋆'_
  isLeftModule (snd FinVecLeftModule) = isLeftModuleR
    where
    isLeftModuleR : IsLeftModule R 0r' _+'_ -'_ _⋆'_
    isLeftModuleR = makeIsLeftModule
      (isSet→ R'.is-set)
      (λ _ _ _ → funExt λ _ → R'.+Assoc _ _ _)
      (λ _ → funExt λ _ → R'.+IdR _)
      (λ _ → funExt λ _ → R'.+InvR _)
      (λ _ _ → funExt λ _ → R'.+Comm _ _)
      (λ _ _ _ → funExt λ _ → sym (R'.·Assoc _ _ _))
      (λ _ _ _ → funExt λ _ → ·DistR+ _ _ _)
      (λ _ _ _ → funExt λ _ → ·DistL+ _ _ _)
      (λ _ → funExt λ _ → R'.·IdL _)
