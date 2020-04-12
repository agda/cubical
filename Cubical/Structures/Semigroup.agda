{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.Semigroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod.Base hiding (_×_) renaming (_×Σ_ to _×_)

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Structures.InftyMagma as M hiding (⟨_⟩)

private
  variable
    ℓ ℓ' : Level

semigroup-axioms : (X : Type ℓ) → ∞-magma-structure X → Type ℓ
semigroup-axioms X _·_ = isSet X ×
                         ((x y z : X) → (x · (y · z)) ≡ ((x · y) · z))

semigroup-structure : Type ℓ → Type ℓ
semigroup-structure = add-to-structure (∞-magma-structure) semigroup-axioms

Semigroup : Type (ℓ-suc ℓ)
Semigroup {ℓ} = TypeWithStr ℓ semigroup-structure

-- Operations for extracting components

Semigroup→∞-Magma : Semigroup {ℓ} → ∞-Magma {ℓ}
Semigroup→∞-Magma (G , _·_ , _) = G , _·_

-- Operations for extracting components

⟨_⟩ : Semigroup → Type ℓ
⟨ G ⟩ = M.⟨ Semigroup→∞-Magma G ⟩

semigroup-operation : (G : Semigroup {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
semigroup-operation G = ∞-magma-operation (Semigroup→∞-Magma G)

module semigroup-operation-syntax where

  semigroup-operation-syntax : (G : Semigroup {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  semigroup-operation-syntax = semigroup-operation

  infixl 20 semigroup-operation-syntax
  syntax semigroup-operation-syntax G x y = x ·⟨ G ⟩ y

open semigroup-operation-syntax

semigroup-isSet : (G : Semigroup {ℓ}) → isSet ⟨ G ⟩
semigroup-isSet (_ , _ , P , _) = P

semigroup-assoc : (G : Semigroup {ℓ})
                → (x y z : ⟨ G ⟩) → (x ·⟨ G ⟩ (y ·⟨ G ⟩ z)) ≡ ((x ·⟨ G ⟩ y) ·⟨ G ⟩ z)
semigroup-assoc (_ , _ , _ , P) = P

-- Semigroup equivalences

semigroup-iso : StrIso semigroup-structure ℓ
semigroup-iso = add-to-iso ∞-magma-structure ∞-magma-iso semigroup-axioms

semigroup-axiom-isProp : (X : Type ℓ)
                       → (s : ∞-magma-structure X)
                       → isProp (semigroup-axioms X s)
semigroup-axiom-isProp X _·_ = isPropΣ isPropIsSet
                               λ isSetX →  isPropPi (λ x → isPropPi (λ y → isPropPi (λ z → isSetX _ _)))

semigroup-is-SNS : SNS {ℓ} semigroup-structure semigroup-iso
semigroup-is-SNS = add-axioms-SNS ∞-magma-structure ∞-magma-iso
                               semigroup-axioms semigroup-axiom-isProp ∞-magma-is-SNS

SemigroupPath : (M N : Semigroup {ℓ}) → (M ≃[ semigroup-iso ] N) ≃ (M ≡ N)
SemigroupPath M N = SIP semigroup-structure semigroup-iso semigroup-is-SNS M N


