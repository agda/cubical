{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.InftyMagma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.NAryOp

open import Cubical.Data.Vec

private
  variable
    ℓ : Level

-- ∞-Magmas with SNS

∞-magma-structure : Type ℓ → Type ℓ
∞-magma-structure X = X → X → X

∞-Magma : Type (ℓ-suc ℓ)
∞-Magma {ℓ} = TypeWithStr ℓ ∞-magma-structure

∞-magma-iso : StrIso ∞-magma-structure ℓ
∞-magma-iso (X , _·_) (Y , _∗_) f =
  (x x' : X) → equivFun f (x · x') ≡ equivFun f x ∗ equivFun f x'

∞-magma-is-SNS : SNS {ℓ} ∞-magma-structure ∞-magma-iso
∞-magma-is-SNS = SNS-≡→SNS-PathP ∞-magma-iso (λ _ _ → funExt₂Equiv)


-- We can also define this using nAryOp

∞-magma-structure' : Type ℓ → Type ℓ
∞-magma-structure' X = nAryOp 2 X X

∞-Magma' : Type (ℓ-suc ℓ)
∞-Magma' {ℓ} = nAryFunStructure 2

∞-magma-iso' : StrIso ∞-magma-structure' ℓ
∞-magma-iso' = nAryFunIso 2

∞-magma-is-SNS' : SNS {ℓ} ∞-magma-structure' ∞-magma-iso'
∞-magma-is-SNS' = nAry-is-SNS 2


-- We can compare the definitions
private

  test1 : (X : Type ℓ) → ∞-magma-structure' X ≡ ∞-magma-structure X
  test1 X = refl

  test2 : ∞-Magma' {ℓ} ≡ ∞-Magma
  test2 = refl

  -- Not refl, but can be proved using currying
  -- test3 : ∞-magma-iso' {ℓ} ≡ ∞-magma-iso
  -- test3 i (X , fX) (Y , fY) f = {!!}
