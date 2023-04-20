{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Coverage where

-- Definition of a coverage on a category, also called a Grothendieck topology.
-- A coverage on a category turns it into a site
-- and enables us to formulate a sheaf condition.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Site.Cover
open import Cubical.Categories.Site.Sieve

module _
  {ℓ ℓ' : Level}
  (C : Category ℓ ℓ')
  where

  open Category C

  record Coverage (ℓcov ℓpat : Level) : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-suc (ℓ-max ℓcov ℓpat)))) where
    no-eta-equality
    field
      covers : (c : ob) → Families.Fam ℓcov (Cover C ℓpat c)
      pullbackStability :
        (c : ob) →
        (cov : ⟨ covers c ⟩) →
        (d : ob) →
        (f : Hom[ d , c ]) →
        ∃[ cov' ∈ ⟨ covers d ⟩ ]
          ⟨ coverRefinesSieve C
              (str (covers d) cov')
              (pulledBackSieve C f (generatedSieve C (str (covers c) cov))) ⟩
