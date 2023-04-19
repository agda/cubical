{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Cover where

-- A cover of an object is just a family of arrows into that object.
-- This notion is used in the definition of a coverage.

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category

module _
  {ℓ ℓ' : Level}
  (C : Category ℓ ℓ')
  where

  open Category C

  record Cover (c : ob) (ℓpat : Level) : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-suc ℓpat))) where
    no-eta-equality
    field
      -- How many patches does the cover consist of?
      patches : Type ℓpat

      patchObj : (pat : patches) → ob
      patchArr : (pat : patches) → Hom[ c , patchObj pat ]
