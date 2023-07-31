{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Sheafification where

-- Construction of the sheafification of a presheaf on a site
-- using a quotient inductive type.

-- TODO: clean up imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Logic using (∀[]-syntax; ∀[∶]-syntax; _⇒_; _⇔_)

open import Cubical.Categories.Category
open import Cubical.Categories.Site.Cover
open import Cubical.Categories.Site.Sieve
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Site.Sheaf
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor

module _
  {ℓ ℓ' ℓcov ℓpat : Level}
  {C : Category ℓ ℓ'}
  (J : Coverage C ℓcov ℓpat)
  {ℓP : Level}
  (P : Presheaf C ℓP)
  where

  open Category C
  open Coverage J

  -- TODO: name
  data S : ob → Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓcov (ℓ-max ℓpat ℓP)))) where

    trunc : {c : ob} → isSet (S c)

    restrict : {c d : ob} → Hom[ d , c ] → S c → S d

    restrictId :
      {c : ob} →
      (x : S c) →
      restrict id x ≡ x
    restrictRestrict :
      {c d e : ob} →
      (f : Hom[ d , c ]) →
      (g : Hom[ e , d ]) →
      (x : S c) →
      restrict (g ⋆ f) x ≡ restrict g (restrict f x)

    η : {c : ob} → ⟨ P ⟅ c ⟆ ⟩ → S c

    ηNatural :
      {c d : ob} →
      (f : Hom[ d , c ]) →
      (x : ⟨ P ⟅ c ⟆ ⟩) →
      restrict f (η x) ≡ η ((P ⟪ f ⟫) x)

    sep :
      {c : ob} →
      (coverName : ⟨ covers c ⟩) →
      let cov = str (covers c) coverName in
      (x y : S c) →
      ((d : ob) → (f : Hom[ d , c ]) → restrict f x ≡ restrict f y) →
      x ≡ y

    amalgamate :
      let
      F : Presheaf C _
      F = record
        { F-ob = λ c → S c , trunc
        ; F-hom = restrict
        ; F-id = funExt restrictId
        ; F-seq = λ f g → funExt (restrictRestrict f g)
        }
      in
      {c : ob} →
      (coverName : ⟨ covers c ⟩) →
      let cov = str (covers c) coverName in
      CompatibleFamilies F cov →
      S c
    restrictAmalgamate :
      let
      F : Presheaf C _
      F = record
        { F-ob = λ c → S c , trunc
        ; F-hom = restrict
        ; F-id = funExt restrictId
        ; F-seq = λ f g → funExt (restrictRestrict f g)
        }
      in
      {c : ob} →
      (coverName : ⟨ covers c ⟩) →
      let cov = str (covers c) coverName in
      (fam : CompatibleFamilies F cov) →
      (i : ⟨ cov ⟩) →
      restrict (patchArr cov i) (amalgamate coverName fam) ≡ fst fam i
