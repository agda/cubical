{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.Semigroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Structures.NAryOp

private
  variable
    ℓ ℓ' : Level

raw-semigroup-structure : Type ℓ → Type ℓ
raw-semigroup-structure X = X → X → X

raw-semigroup-is-SNS : SNS {ℓ} raw-semigroup-structure _
raw-semigroup-is-SNS = nAryFunSNS 2

semigroup-axioms : (X : Type ℓ) → raw-semigroup-structure X → Type ℓ
semigroup-axioms X _·_ = isSet X ×
                         ((x y z : X) → (x · (y · z)) ≡ ((x · y) · z))

semigroup-structure : Type ℓ → Type ℓ
semigroup-structure = add-to-structure (raw-semigroup-structure) semigroup-axioms

Semigroup : Type (ℓ-suc ℓ)
Semigroup {ℓ} = TypeWithStr ℓ semigroup-structure

-- Operations for extracting components

⟨_⟩ : Semigroup → Type ℓ
⟨ G , _ ⟩ = G

semigroup-operation : (G : Semigroup {ℓ}) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
semigroup-operation (_ , f , _) = f

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
semigroup-iso = add-to-iso (nAryFunIso 2) semigroup-axioms

semigroup-axiom-isProp : (X : Type ℓ)
                       → (s : raw-semigroup-structure X)
                       → isProp (semigroup-axioms X s)
semigroup-axiom-isProp X _·_ = isPropΣ isPropIsSet
                               λ isSetX →  isPropΠ (λ x → isPropΠ (λ y → isPropΠ (λ z → isSetX _ _)))

semigroup-is-SNS : SNS {ℓ} semigroup-structure semigroup-iso
semigroup-is-SNS = add-axioms-SNS _ semigroup-axiom-isProp (nAryFunSNS 2)

SemigroupPath : (M N : Semigroup {ℓ}) → (M ≃[ semigroup-iso ] N) ≃ (M ≡ N)
SemigroupPath = SIP semigroup-is-SNS

-- Semigroup ·syntax

module semigroup-·syntax (G : Semigroup {ℓ}) where

  infixr 18 _·_

  _·_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  _·_ = semigroup-operation G
