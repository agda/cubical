{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.AbGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod.Base hiding (_×_) renaming (_×Σ_ to _×_)
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.InftyMagma
open import Cubical.Structures.Group

private
  variable
    ℓ : Level

abelian-group-axioms : (X : Type ℓ) → ∞-magma-structure X → Type ℓ
abelian-group-axioms X _·_ = group-axioms X _·_ ×
                             ((x y : X) → x · y ≡ y · x)

abelian-group-structure : Type ℓ → Type ℓ
abelian-group-structure = add-to-structure ∞-magma-structure abelian-group-axioms

AbGroups : Type (ℓ-suc ℓ)
AbGroups {ℓ} = TypeWithStr ℓ abelian-group-structure


abelian-group-iso : StrIso abelian-group-structure ℓ
abelian-group-iso = add-to-iso ∞-magma-structure ∞-magma-iso abelian-group-axioms

abelian-group-axioms-isProp : (X : Type ℓ)
                           → (s : ∞-magma-structure X)
                           → isProp (abelian-group-axioms X s)
abelian-group-axioms-isProp X _·_ = isPropΣ (group-axioms-isProp X _·_)
                                    λ { (isSetX , _) → isPropPi (λ x → isPropPi (λ y → isSetX (x · y) (y · x)))}

abelian-group-is-SNS : SNS {ℓ} abelian-group-structure abelian-group-iso
abelian-group-is-SNS = add-axioms-SNS ∞-magma-structure ∞-magma-iso
                       abelian-group-axioms abelian-group-axioms-isProp ∞-magma-is-SNS

AbGroupPath : (M N : AbGroups {ℓ}) → (M ≃[ abelian-group-iso ] N) ≃ (M ≡ N)
AbGroupPath M N = SIP abelian-group-structure abelian-group-iso abelian-group-is-SNS M N
