{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Rng where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.NAryOp
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.AbGroup

private
  variable
    ℓ ℓ' : Level

raw-rng-structure : Type ℓ → Type ℓ
raw-rng-structure X = (X → X → X) × (X → X → X)

raw-rng-is-SNS : SNS {ℓ} raw-rng-structure _
raw-rng-is-SNS = join-SNS (nAryFunIso 2) (nAryFunSNS 2) (nAryFunIso 2) (nAryFunSNS 2)

rng-axioms : (X : Type ℓ) (s : raw-rng-structure X) → Type ℓ
rng-axioms X (_·_ , _+_) = abelian-group-axioms X _·_ ×
                           semigroup-axioms X _+_ ×
                           ((x y z : X) → x · (y + z) ≡ (x · y) + (x · z)) ×
                           ((x y z : X) → (x + y) · z ≡ (x · z) + (y · z))

rng-structure : Type ℓ → Type ℓ
rng-structure = add-to-structure raw-rng-structure rng-axioms


Rngs : Type (ℓ-suc ℓ)
Rngs {ℓ} = TypeWithStr ℓ rng-structure

rng-iso : StrIso rng-structure ℓ
rng-iso = add-to-iso (join-iso (nAryFunIso 2) (nAryFunIso 2)) rng-axioms

rng-axioms-isProp : (X : Type ℓ) (s : raw-rng-structure X) → isProp (rng-axioms X s)
rng-axioms-isProp X (_·_ , _+_) = isPropΣ (abelian-group-axioms-isProp X _·_)
                                  λ _ → isPropΣ (semigroup-axiom-isProp X _+_)
                                  λ { (isSetX , _) → isPropΣ (isPropΠ3 (λ _ _ _ → isSetX _ _))
                                  λ _ → isPropΠ3 (λ _ _ _ → isSetX _ _)}

rng-is-SNS : SNS {ℓ} rng-structure rng-iso
rng-is-SNS = add-axioms-SNS _ rng-axioms-isProp raw-rng-is-SNS

RngPath : (M N : Rngs {ℓ}) → (M ≃[ rng-iso ] N) ≃ (M ≡ N)
RngPath = SIP rng-is-SNS
