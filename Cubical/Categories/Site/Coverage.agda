{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Coverage where

-- Definition of a coverage on a category, also called a Grothendieck topology.
-- A coverage on a category turns it into a site
-- and enables us to formulate a sheaf condition.

-- We stay close to the definitions given in the nLab and the Elephant:
-- * https://ncatlab.org/nlab/show/coverage
-- * Peter Johnstone, "Sketches of an Elephant" (Definition C2.1.1)

-- While the covers are just families of arrows,
-- we use the notion of sieves to express the "pullback stability" property of the coverage.

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
      covers : (c : ob) → TypeWithStr ℓcov λ Cov → Cov → (Cover C ℓpat c)
      pullbackStability :
        {c : ob} →
        (cov : ⟨ covers c ⟩) →
        {d : ob} →
        (f : Hom[ d , c ]) →
        ∃[ cov' ∈ ⟨ covers d ⟩ ]
          coverRefinesSieve
            (str (covers d) cov')
            (pulledBackSieve f (generatedSieve (str (covers c) cov)))
