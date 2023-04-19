{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Cover where

-- A cover of an object is just a family of arrows into that object.
-- This notion is used in the definition of a coverage.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Slice

module Families {ℓX : Level} where

  Fam : (ℓ : Level) → Type ℓX → Type (ℓ-max ℓX (ℓ-suc ℓ))
  Fam ℓ X = TypeWithStr ℓ (λ Y → (Y → X))

open Families

module _
  {ℓ ℓ' : Level}
  (C : Category ℓ ℓ')
  where

  open Category

  Cover : (ℓ'' : Level) → ob C → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ''))
  Cover ℓ'' c = Fam ℓ'' (ob (SliceCat C c))

  -- Extracting the members (patches) from a cover.
  module _
    {ℓ'' : Level}
    {c : ob C}
    (cov : Cover ℓ'' c)
    (i : ⟨ cov ⟩)
    where

    patchObj : ob C
    patchObj = S-ob (str cov i)

    patchArr : C [ patchObj , c ]
    patchArr = S-arr (str cov i)
