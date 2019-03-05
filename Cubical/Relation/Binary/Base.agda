{-# OPTIONS --cubical --safe #-}
module Cubical.Relation.Binary.Base where

open import Cubical.Core.Prelude hiding (refl; sym)
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetQuotients.Base
open import Cubical.Core.Glue hiding (isEquiv)

module BinaryRelation {ℓ ℓ' : Level} {A : Set ℓ} (R : A → A → hProp {ℓ = ℓ'}) where
  isRefl : Set (ℓ-max ℓ ℓ')
  isRefl = {a : A} → fst (R a a)

  isSym : Set (ℓ-max ℓ ℓ')
  isSym = {a b : A} → fst (R a b) → fst (R b a)

  isTrans : Set (ℓ-max ℓ ℓ')
  isTrans = {a b c : A}  → fst (R a b) → fst (R b c) → fst (R a c)

  record isEquiv : Set (ℓ-max ℓ ℓ') where
    constructor Equiv
    field
      refl : isRefl
      sym : isSym
      trans : isTrans

  isEffective : Set (ℓ-max ℓ ℓ')
  isEffective = (a b : A) →
    let x : A / R
        x = [ a ]
        y : A / R
        y = [ b ]
    in (x ≡ y) ≃ fst (R a b)
