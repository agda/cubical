{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.SievesAsFunctors where

-- There are also sieves in Cubical.Site.Sieve

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open Category
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Propositions
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.Thin

private
  variable
    ℓ ℓ' ℓP : Level
    C : Category ℓ ℓ'

SIEVE : (C : Category ℓ ℓ') → (ℓP : Level)
  → Category (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓP)) (ℓ-max (ℓ-max ℓ ℓ') ℓP)
SIEVE C ℓP = FUNCTOR (C ^op) (PROP ℓP)

Sieve : (C : Category ℓ ℓ') → (ℓP : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓP))
Sieve C ℓP = SIEVE C ℓP .ob

isThinSIEVE : isThin (SIEVE C ℓP)
isThinSIEVE = isThinFUNCTOR _ _ isThinPROP

SIEVE_ON : (C : Category ℓ ℓ') → (c : C .ob) → (ℓP : Level)
  → Category (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓP)) (ℓ-max (ℓ-max ℓ ℓ') ℓP)
SIEVE_ON C c ℓP = SIEVE (SliceCat C c) ℓP
