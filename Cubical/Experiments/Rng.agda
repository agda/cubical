-- This file needs to be rewritten so that Rng's are defined as a
-- record (as is the case for other algebraic structures like
-- rings). As this file isn't used for anything at the moment this
-- rewrite has been postponed.

{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Rng where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.Macro
open import Cubical.Structures.Semigroup hiding (⟨_⟩)
open import Cubical.Structures.AbGroup

private
  variable
    ℓ ℓ' : Level

module _ {ℓ} where
  open Macro ℓ (recvar (recvar var) , recvar (recvar var)) public renaming
    ( structure to raw-rng-structure
    ; iso to raw-rng-iso
    ; isSNS to raw-rng-is-SNS
    )

rng-axioms : (X : Type ℓ) (s : raw-rng-structure X) → Type ℓ
rng-axioms X (_·_ , _+_) = abelian-group-axioms X _·_ ×
                           SemigroupΣ-theory.semigroup-axioms X _+_ ×
                           ((x y z : X) → x · (y + z) ≡ (x · y) + (x · z)) ×
                           ((x y z : X) → (x + y) · z ≡ (x · z) + (y · z))

rng-structure : Type ℓ → Type ℓ
rng-structure = AxiomStructure raw-rng-structure rng-axioms


Rngs : Type (ℓ-suc ℓ)
Rngs {ℓ} = TypeWithStr ℓ rng-structure

rng-iso : StrIso rng-structure ℓ
rng-iso = AxiomIso raw-rng-iso rng-axioms

rng-axioms-isProp : (X : Type ℓ) (s : raw-rng-structure X) → isProp (rng-axioms X s)
rng-axioms-isProp X (_·_ , _+_) = isPropΣ (abelian-group-axioms-isProp X _·_)
                                  λ _ → isPropΣ (SemigroupΣ-theory.semigroup-axioms-isProp X _+_)
                                  λ { (isSetX , _) → isPropΣ (isPropΠ3 (λ _ _ _ → isSetX _ _))
                                  λ _ → isPropΠ3 (λ _ _ _ → isSetX _ _)}

rng-is-SNS : SNS {ℓ} rng-structure rng-iso
rng-is-SNS = axiomUnivalentStr _ rng-axioms-isProp raw-rng-is-SNS

RngPath : (M N : Rngs {ℓ}) → (M ≃[ rng-iso ] N) ≃ (M ≡ N)
RngPath = SIP rng-is-SNS
