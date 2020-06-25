{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.PropositionalTruncation

Rel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Rel A B ℓ' = A → B → Type ℓ'

PropRel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
PropRel A B ℓ' = Σ[ R ∈ Rel A B ℓ' ] ∀ a b → isProp (R a b)

invPropRel : ∀ {ℓ ℓ'} {A B : Type ℓ}
  → PropRel A B ℓ' → PropRel B A ℓ'
invPropRel R .fst b a = R .fst a b
invPropRel R .snd b a = R .snd a b

compPropRel : ∀ {ℓ ℓ' ℓ''} {A B C : Type ℓ}
  → PropRel A B ℓ' → PropRel B C ℓ'' → PropRel A C (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
compPropRel R S .fst a c = ∥ Σ[ b ∈ _ ] (R .fst a b × S .fst b c) ∥
compPropRel R S .snd _ _ = squash

graphRel : ∀ {ℓ} {A B : Type ℓ} → (A → B) → Rel A B ℓ
graphRel f a b = f a ≡ b

module BinaryRelation {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') where
  isRefl : Type (ℓ-max ℓ ℓ')
  isRefl = (a : A) → R a a

  isSym : Type (ℓ-max ℓ ℓ')
  isSym = (a b : A) → R a b → R b a

  isTrans : Type (ℓ-max ℓ ℓ')
  isTrans = (a b c : A)  → R a b → R b c → R a c

  record isEquivRel : Type (ℓ-max ℓ ℓ') where
    constructor equivrel
    field
      reflexive : isRefl
      symmetric : isSym
      transitive : isTrans

  isPropValued : Type (ℓ-max ℓ ℓ')
  isPropValued = (a b : A) → isProp (R a b)

  isEffective : Type (ℓ-max ℓ ℓ')
  isEffective =
    (a b : A) → isEquiv (eq/ {R = R} a b)

EquivRel : ∀ {ℓ} (A : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
EquivRel A ℓ' = Σ[ R ∈ Rel A A ℓ' ] BinaryRelation.isEquivRel R

EquivPropRel : ∀ {ℓ} (A : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
EquivPropRel A ℓ' = Σ[ R ∈ PropRel A A ℓ' ] BinaryRelation.isEquivRel (R .fst)

