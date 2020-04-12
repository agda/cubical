{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Ring where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod.Base hiding (_×_) renaming (_×Σ_ to _×_)

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.InftyMagma hiding (⟨_⟩)
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.AbGroup

private
  variable
    ℓ ℓ' : Level

raw-rng-structure : Type ℓ → Type ℓ
raw-rng-structure X = (X → X → X) × (X → X → X)

raw-rng-iso : StrIso raw-rng-structure ℓ
raw-rng-iso (R , _·_ , _+_) (S , _⊙_ , _⊕_) f =
  ((x y : R) → equivFun f (x · y) ≡ equivFun f x ⊙ equivFun f y) ×
  ((x y : R) → equivFun f (x + y) ≡ equivFun f x ⊕ equivFun f y)

raw-rng-is-SNS : SNS {ℓ} raw-rng-structure raw-rng-iso
raw-rng-is-SNS = join-SNS ∞-magma-structure ∞-magma-iso ∞-magma-is-SNS
                          ∞-magma-structure ∞-magma-iso ∞-magma-is-SNS

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
rng-iso = add-to-iso raw-rng-structure raw-rng-iso rng-axioms

rng-axioms-isProp : (X : Type ℓ) (s : raw-rng-structure X) → isProp (rng-axioms X s)
rng-axioms-isProp X (_·_ , _+_) = isPropΣ (abelian-group-axioms-isProp X _·_)
                                  λ _ → isPropΣ (semigroup-axiom-isProp X _+_)
                                  λ { (isSetX , _) → isPropΣ (isPropPi λ _ → isPropPi λ _ → isPropPi λ _ → isSetX _ _)
                                  λ _ → isPropPi λ _ → isPropPi λ _ → isPropPi λ _ → isSetX _ _}

rng-is-SNS : SNS {ℓ} rng-structure rng-iso
rng-is-SNS = add-axioms-SNS raw-rng-structure raw-rng-iso
                                   rng-axioms rng-axioms-isProp raw-rng-is-SNS
                                   
RngPath : (M N : Rngs {ℓ}) → (M ≃[ rng-iso ] N) ≃ (M ≡ N)
RngPath M N = SIP rng-structure rng-iso rng-is-SNS M N
