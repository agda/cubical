{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.InftyMagma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

private
  variable
    ℓ ℓ' ℓ'' : Level

-- ∞-Magmas with SNS

∞-magma-structure : Type ℓ → Type ℓ
∞-magma-structure X = X → X → X

∞-Magma : Type (ℓ-suc ℓ)
∞-Magma {ℓ} = TypeWithStr ℓ ∞-magma-structure

∞-magma-iso : StrIso ∞-magma-structure ℓ
∞-magma-iso (X , _·_) (Y , _∗_) f =
  (x x' : X) → equivFun f (x · x') ≡ equivFun f x ∗ equivFun f x'

∞-magma-is-SNS : SNS {ℓ} ∞-magma-structure ∞-magma-iso
∞-magma-is-SNS f = SNS-≡→SNS-PathP ∞-magma-iso (λ _ _ → funExt₂Equiv) f
