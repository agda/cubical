{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Ring where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.NAryOp
open import Cubical.Structures.Monoid hiding (⟨_⟩)
open import Cubical.Structures.AbGroup
open import Cubical.Structures.Pointed

private
  variable
    ℓ ℓ' : Level

raw-ring-structure : Type ℓ → Type ℓ
raw-ring-structure X = (X → X → X) × X × (X → X → X)

-- Maybe this is not the best way? (Suggestions welcome, maybe having raw-monoid-iso defined?)
raw-ring-is-SNS : SNS {ℓ} raw-ring-structure _
raw-ring-is-SNS = join-SNS (nAryFunIso 2) (nAryFunSNS 2)
                           (join-iso pointed-iso (nAryFunIso 2))
                           (join-SNS pointed-iso pointed-is-SNS (nAryFunIso 2) (nAryFunSNS 2))

ring-axioms : (X : Type ℓ) (s : raw-ring-structure X) → Type ℓ
ring-axioms X (_+_ , ₁ , _·_) = abelian-group-axioms X _+_ ×
                                monoid-axioms X (₁ , _·_) ×
                                ((x y z : X) → x · (y + z) ≡ (x · y) + (x · z)) ×
                                ((x y z : X) → (x + y) · z ≡ (x · z) + (y · z))

ring-structure : Type ℓ → Type ℓ
ring-structure = add-to-structure raw-ring-structure ring-axioms

Ring : Type (ℓ-suc ℓ)
Ring {ℓ} = TypeWithStr ℓ ring-structure

ring-iso : StrIso ring-structure ℓ
ring-iso = add-to-iso (join-iso (nAryFunIso 2) (join-iso pointed-iso (nAryFunIso 2))) ring-axioms

ring-axioms-isProp : (X : Type ℓ) (s : raw-ring-structure X) → isProp (ring-axioms X s)
ring-axioms-isProp X (_+_ , ₁ , _·_) = isPropΣ (abelian-group-axioms-isProp X _+_)
                                      λ _ → isPropΣ (monoid-axioms-are-Props X (₁ , _·_))
                                      λ { (isSetX , _) → isPropΣ (isPropΠ3 (λ _ _ _ → isSetX _ _))
                                      λ _ → isPropΠ3 (λ _ _ _ → isSetX _ _)}

ring-is-SNS : SNS {ℓ} ring-structure ring-iso
ring-is-SNS = add-axioms-SNS _ ring-axioms-isProp raw-ring-is-SNS

RingPath : (M N : Ring {ℓ}) → (M ≃[ ring-iso ] N) ≃ (M ≡ N)
RingPath = SIP ring-is-SNS
