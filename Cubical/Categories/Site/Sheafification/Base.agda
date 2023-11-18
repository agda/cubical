{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Sheafification.Base where

-- Construction of the sheafification of a presheaf on a site
-- using a quotient inductive type (QIT).

-- This is inspired by the construction of the sheafification (for finite coverings) in:
-- * E. Palmgren, S.J. Vickers, "Partial Horn logic and cartesian categories"

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open import Cubical.Data.Sigma

open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor

open import Cubical.Categories.Site.Cover
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Site.Sheaf


module Sheafification
  {ℓ ℓ' ℓcov ℓpat : Level}
  {C : Category ℓ ℓ'}
  (J : Coverage C ℓcov ℓpat)
  {ℓP : Level}
  (P : Presheaf C ℓP)
  where

  open Category C hiding (_∘_)
  open Coverage J

  data ⟨sheafification⟅_⟆⟩ : ob → Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓcov (ℓ-max ℓpat ℓP)))) where

    trunc : {c : ob} → isSet ⟨sheafification⟅ c ⟆⟩

    restrict : {c d : ob} → (f : Hom[ d , c ]) → ⟨sheafification⟅ c ⟆⟩ → ⟨sheafification⟅ d ⟆⟩

    restrictId :
      {c : ob} →
      (x : ⟨sheafification⟅ c ⟆⟩) →
      restrict id x ≡ x
    restrictRestrict :
      {c d e : ob} →
      (f : Hom[ d , c ]) →
      (g : Hom[ e , d ]) →
      (x : ⟨sheafification⟅ c ⟆⟩) →
      restrict (g ⋆ f) x ≡ restrict g (restrict f x)

    η⟦⟧ : {c : ob} → (x : ⟨ P ⟅ c ⟆ ⟩) → ⟨sheafification⟅ c ⟆⟩

    ηNatural :
      {c d : ob} →
      (f : Hom[ d , c ]) →
      (x : ⟨ P ⟅ c ⟆ ⟩) →
      η⟦⟧ ((P ⟪ f ⟫) x) ≡ restrict f (η⟦⟧ x)

    sep :
      {c : ob} →
      (cover : ⟨ covers c ⟩) →
      let cov = str (covers c) cover in
      (x y : ⟨sheafification⟅ c ⟆⟩) →
      (x~y :
        (patch : ⟨ cov ⟩) →
        restrict (patchArr cov patch) x ≡ restrict (patchArr cov patch) y) →
      x ≡ y

    amalgamate :
      let
      -- Is there any way to make this definition now and reuse it later?
      sheafification : Presheaf C _
      sheafification = record
        { F-ob = λ c → ⟨sheafification⟅ c ⟆⟩ , trunc
        ; F-hom = restrict
        ; F-id = funExt restrictId
        ; F-seq = λ f g → funExt (restrictRestrict f g)
        }
      in
      {c : ob} →
      (cover : ⟨ covers c ⟩) →
      let cov = str (covers c) cover in
      (fam : CompatibleFamily sheafification cov) →
      ⟨sheafification⟅ c ⟆⟩
    restrictAmalgamate :
      let
      sheafification : Presheaf C _
      sheafification = record
        { F-ob = λ c → ⟨sheafification⟅ c ⟆⟩ , trunc
        ; F-hom = restrict
        ; F-id = funExt restrictId
        ; F-seq = λ f g → funExt (restrictRestrict f g)
        }
      in
      {c : ob} →
      (cover : ⟨ covers c ⟩) →
      let cov = str (covers c) cover in
      (fam : CompatibleFamily sheafification cov) →
      (patch : ⟨ cov ⟩) →
      restrict (patchArr cov patch) (amalgamate cover fam) ≡ fst fam patch

  sheafification : Presheaf C (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓcov) ℓpat) ℓP)
  Functor.F-ob sheafification c = ⟨sheafification⟅ c ⟆⟩ , trunc
  Functor.F-hom sheafification = restrict
  Functor.F-id sheafification = funExt restrictId
  Functor.F-seq sheafification f g = funExt (restrictRestrict f g)

  isSheafSheafification : isSheaf J sheafification
  isSheafSheafification c cover = isEmbedding×isSurjection→isEquiv
    ( injEmbedding
        (isSetCompatibleFamily sheafification cov)
        (λ {x} {y} x~y → sep cover x y (funExt⁻ (cong fst x~y)))
    , λ fam →
        ∣ amalgamate cover fam
        , Σ≡Prop
            (isPropIsCompatibleFamily sheafification cov)
            (funExt (restrictAmalgamate cover fam)) ∣₁ )
    where
    cov = str (covers c) cover
