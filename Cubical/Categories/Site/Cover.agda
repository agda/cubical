{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Cover where

-- A cover of an object is just a family of arrows into that object.
-- This notion is used in the definition of a coverage.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Slice


module _
  {ℓ ℓ' : Level}
  (C : Category ℓ ℓ')
  where

  open Category

  Cover : (ℓpat : Level) → ob C → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓpat))
  Cover ℓpat c = TypeWithStr ℓpat λ patches → patches → ob (SliceCat C c)

module _
  {ℓ ℓ' : Level}
  {C : Category ℓ ℓ'}
  where

  open Category

  -- Extracting the members (patches) from a cover.
  module _
    {ℓpat : Level}
    {c : ob C}
    (cov : Cover C ℓpat c)
    (patch : ⟨ cov ⟩)
    where

    patchObj : ob C
    patchObj = S-ob (str cov patch)

    patchArr : C [ patchObj , c ]
    patchArr = S-arr (str cov patch)
