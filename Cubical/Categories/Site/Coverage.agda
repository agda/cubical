{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Coverage where

-- Definition of a coverage on a category, also called a Grothendieck topology.
-- A coverage on a category turns it into a site
-- and enables us to formulate a sheaf condition.

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Site.Cover

module _
  {ℓ ℓ' : Level}
  (C : Category ℓ ℓ')
  where

  open Category C
  open Cover


  record Coverage (ℓcov ℓpat : Level) : Type _ where -- (ℓ-max ℓ (ℓ-max ℓ' (ℓ-suc ℓcov))) where
    no-eta-equality
    field
      -- How many generating covers does a given object have?
      covers : ob → Type ℓcov

      -- Note: We could want to have one global index set of generating covers
      -- instead of one index set per object. If this index set is required to be a set,
      -- it might be unclear how to define a maximal coverage, where every object
      -- has an empty cover, when ob is not a set.

      cover : {c : ob} (cov : covers c) → Cover C c ℓpat

      pullbackStability :
        (c : ob) →
        (cov : covers c) →
        (d : ob) →
        (f : Hom[ d , c ]) →
        ∥ (Σ[ cov' ∈ covers d ]
          ((pat : patches (cover cov')) → {!!}))
        ∥₁
