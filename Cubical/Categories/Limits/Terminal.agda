{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Limits.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
-- open import Cubical.Categories.Limits.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓ ℓ' : Level

module _ (C : Precategory ℓ ℓ') where
  open Precategory C

  isInitial : (x : ob) → Type (ℓ-max ℓ ℓ')
  isInitial x = ∀ (y : ob) → isContr (C [ x , y ])

  isFinal : (x : ob) → Type (ℓ-max ℓ ℓ')
  isFinal x = ∀ (y : ob) → isContr (C [ y , x ])

  hasFinalOb : Type (ℓ-max ℓ ℓ')
  hasFinalOb = Σ[ x ∈ ob ] isFinal x
