{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.Monoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.Pointed
open import Cubical.Structures.NAryOp

private
  variable
    ℓ : Level

-- Monoids
raw-monoid-structure : Type ℓ → Type ℓ
raw-monoid-structure X = X × (X → X → X)

-- If we ignore the axioms we get a "raw" monoid
raw-monoid-is-SNS : SNS {ℓ} raw-monoid-structure _
raw-monoid-is-SNS = join-SNS pointed-iso pointed-is-SNS (nAryFunIso 2) (nAryFunSNS 2)

-- Monoid axioms
monoid-axioms : (X : Type ℓ) → raw-monoid-structure X → Type ℓ
monoid-axioms X (e , _·_ ) = isSet X
                           × ((x y z : X) → x · (y · z) ≡ (x · y) · z)
                           × ((x : X) → x · e ≡ x)
                           × ((x : X) → e · x ≡ x)

monoid-structure : Type ℓ → Type ℓ
monoid-structure = add-to-structure raw-monoid-structure monoid-axioms

Monoids : Type (ℓ-suc ℓ)
Monoids {ℓ} = TypeWithStr ℓ monoid-structure

monoid-iso : StrIso monoid-structure ℓ
monoid-iso = add-to-iso (join-iso pointed-iso (nAryFunIso 2)) monoid-axioms

-- We have to show that the monoid axioms are indeed propositions
monoid-axioms-are-Props : (X : Type ℓ) (s : raw-monoid-structure X) → isProp (monoid-axioms X s)
monoid-axioms-are-Props X (e , _·_) s = β s
   where
   α = s .fst
   β = isProp× isPropIsSet
      (isProp× (isPropΠ3 (λ x y z → α (x · (y · z)) ((x · y) · z)))
      (isProp× (isPropΠ (λ x → α (x · e) x)) (isPropΠ (λ x → α (e · x) x))))

monoid-is-SNS : SNS {ℓ} monoid-structure monoid-iso
monoid-is-SNS = add-axioms-SNS _ monoid-axioms-are-Props raw-monoid-is-SNS

MonoidPath : (M N : Monoids {ℓ}) → (M ≃[ monoid-iso ] N) ≃ (M ≡ N)
MonoidPath = SIP monoid-is-SNS
