{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.Binary.Base where

open import Cubical.Core.Prelude hiding (refl; sym) renaming (isProp to isProp')
open import Cubical.Foundations.HLevels 
open import Cubical.HITs.SetQuotients.Base
open import Cubical.Core.Glue hiding (isEquiv)

module BinaryRelation {ℓ ℓ' : Level} {A : Set ℓ} (R : A → A → Set ℓ') where
  isRefl : Set (ℓ-max ℓ ℓ')
  isRefl = {a : A} → R a a

  isSym : Set (ℓ-max ℓ ℓ')
  isSym = {a b : A} → R a b → R b a

  isTrans : Set (ℓ-max ℓ ℓ')
  isTrans = {a b c : A}  → R a b → R b c → R a c

  record isEquiv : Set (ℓ-max ℓ ℓ') where
    constructor Equiv
    field
      refl : isRefl
      sym : isSym
      trans : isTrans

  isProp : Set (ℓ-max ℓ ℓ')
  isProp = (a b : A) → isProp' (R a b)

  isEffective : Set (ℓ-max ℓ ℓ')
  isEffective = (a b : A) →
    let x : A / R
        x = [ a ]
        y : A / R
        y = [ b ]
    in (x ≡ y) ≃ R a b
