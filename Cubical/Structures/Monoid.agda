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

Monoid : Type (ℓ-suc ℓ)
Monoid {ℓ} = TypeWithStr ℓ monoid-structure

-- Monoid extractors

⟨_⟩ : Monoid {ℓ} → Type ℓ
⟨ G , _ ⟩ = G

monoid-id : (M : Monoid {ℓ}) → ⟨ M ⟩
monoid-id (_ , (e , _) , _) = e

monoid-operation : (M : Monoid {ℓ}) → ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
monoid-operation (_ , (_ , f) , _) = f

-- Monoid syntax with explicit monoid

module monoid-syntax where
  id : (M : Monoid {ℓ}) → ⟨ M ⟩
  id = monoid-id

  monoid-operation-syntax : (M : Monoid {ℓ}) → ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
  monoid-operation-syntax = monoid-operation

  infixr 18 monoid-operation-syntax
  syntax monoid-operation-syntax M x y = x ·⟨ M ⟩ y

open monoid-syntax

-- More Monoid extractors

monoid-is-set : (M : Monoid {ℓ}) → isSet (⟨ M ⟩)
monoid-is-set (_ , _ , P , _) = P

monoid-assoc : (M : Monoid {ℓ})
             → (x y z : ⟨ M ⟩) → x ·⟨ M ⟩ (y ·⟨ M ⟩ z) ≡ (x ·⟨ M ⟩ y) ·⟨ M ⟩ z
monoid-assoc (_ , _ , _ , P , _) = P

monoid-rid : (M : Monoid {ℓ})
           → (x : ⟨ M ⟩) → x ·⟨ M ⟩ (id M) ≡ x
monoid-rid (_ , _ , _ , _ , P , _) = P

monoid-lid : (M : Monoid {ℓ})
           → (x : ⟨ M ⟩) → (id M) ·⟨ M ⟩ x ≡ x
monoid-lid (_ , _ , _ , _ , _ , P) = P

-- Monoid equivalence
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

MonoidPath : (M N : Monoid {ℓ}) → (M ≃[ monoid-iso ] N) ≃ (M ≡ N)
MonoidPath = SIP monoid-is-SNS

-- Added for its use in groups
-- If there exists a inverse of an element it is unique

inv-lemma : (M : Monoid {ℓ})
          → (x y z : ⟨ M ⟩)
          → y ·⟨ M ⟩ x ≡ id M
          → x ·⟨ M ⟩ z ≡ id M
          → y ≡ z
inv-lemma M x y z left-inverse right-inverse =
  y                     ≡⟨ sym (monoid-rid M y) ⟩
  y ·⟨ M ⟩ id M         ≡⟨ cong (λ - → y ·⟨ M ⟩ -) (sym right-inverse) ⟩
  y ·⟨ M ⟩ (x ·⟨ M ⟩ z) ≡⟨ monoid-assoc M y x z ⟩
  (y ·⟨ M ⟩ x) ·⟨ M ⟩ z ≡⟨ cong (λ - → - ·⟨ M ⟩ z) left-inverse ⟩
  id M ·⟨ M ⟩ z         ≡⟨ monoid-lid M z ⟩
  z ∎

-- Monoid ·syntax

module monoid-·syntax (M : Monoid {ℓ}) where

  infixr 18 _·_

  _·_ : ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
  _·_ = monoid-operation M

  ₁ : ⟨ M ⟩
  ₁ = monoid-id M
