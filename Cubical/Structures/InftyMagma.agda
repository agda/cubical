{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.InftyMagma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.FunExtEquiv

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

private
  variable
    ℓ ℓ' ℓ'' : Level

-- ∞-Magmas with SNS

∞-magma-structure : Type ℓ → Type ℓ
∞-magma-structure X = X → X → X

∞-Magma : Type (ℓ-suc ℓ)
∞-Magma {ℓ} = TypeWithStr ℓ ∞-magma-structure

-- Operations for extracting components


⟨_⟩ : ∞-Magma {ℓ} → Type ℓ
⟨ G , _·_ ⟩ = G

∞-magma-operation : (X : ∞-Magma {ℓ}) → ⟨ X ⟩ → ⟨ X ⟩ → ⟨ X ⟩
∞-magma-operation (G , _·_) = _·_

-- Special notation, hidden in a module in order to not import it by default

module ∞-magma-operation-syntax where

  ∞-magma-operation-syntax : (X : ∞-Magma {ℓ}) → ⟨ X ⟩ → ⟨ X ⟩ → ⟨ X ⟩
  ∞-magma-operation-syntax (G , _·_) = _·_

  infix 20 ∞-magma-operation-syntax
  syntax ∞-magma-operation-syntax X x y = x ·⟨ X ⟩ y

-- Equivalences of ∞-magma

∞-magma-iso : StrIso ∞-magma-structure ℓ
∞-magma-iso (X , _·_) (Y , _∗_) f =
  (x x' : X) → equivFun f (x · x') ≡ equivFun f x ∗ equivFun f x'

∞-magma-is-SNS : SNS {ℓ} ∞-magma-structure ∞-magma-iso
∞-magma-is-SNS f = SNS-≡→SNS-PathP ∞-magma-iso (λ _ _ → funExt₂Equiv) f


