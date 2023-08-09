{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Sheafification where

-- Construction of the sheafification of a presheaf on a site
-- using a quotient inductive type.

-- This is inspired by the construction of the sheafification (for finite coverings) in:
-- * E. Palmgren, S.J. Vickers, "Partial Horn logic and cartesian categories"

-- TODO: clean up imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open import Cubical.Data.Sigma

open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

open import Cubical.Categories.Category
open import Cubical.Categories.Site.Cover
open import Cubical.Categories.Site.Sieve
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Site.Sheaf
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

module Sheafification
  {ℓ ℓ' ℓcov ℓpat : Level}
  {C : Category ℓ ℓ'}
  (J : Coverage C ℓcov ℓpat)
  {ℓP : Level}
  (P : Presheaf C ℓP)
  where

  open Category C hiding (_∘_)
  open Coverage J

  data ⟨F⟅_⟆⟩ : ob → Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓcov (ℓ-max ℓpat ℓP)))) where

    trunc : {c : ob} → isSet ⟨F⟅ c ⟆⟩

    restrict : {c d : ob} → Hom[ d , c ] → ⟨F⟅ c ⟆⟩ → ⟨F⟅ d ⟆⟩

    restrictId :
      {c : ob} →
      (x : ⟨F⟅ c ⟆⟩) →
      restrict id x ≡ x
    restrictRestrict :
      {c d e : ob} →
      (f : Hom[ d , c ]) →
      (g : Hom[ e , d ]) →
      (x : ⟨F⟅ c ⟆⟩) →
      restrict (g ⋆ f) x ≡ restrict g (restrict f x)

    η⟦_⟧ : {c : ob} → ⟨ P ⟅ c ⟆ ⟩ → ⟨F⟅ c ⟆⟩

    ηNatural :
      {c d : ob} →
      (f : Hom[ d , c ]) →
      (x : ⟨ P ⟅ c ⟆ ⟩) →
      η⟦ (P ⟪ f ⟫) x ⟧ ≡ restrict f (η⟦ x ⟧)

    sep :
      {c : ob} →
      (cover : ⟨ covers c ⟩) →
      let cov = str (covers c) cover in
      (x y : ⟨F⟅ c ⟆⟩) →
      ((i : ⟨ cov ⟩) → restrict (patchArr cov i) x ≡ restrict (patchArr cov i) y) →
      x ≡ y

    amalgamate :
      let
      -- Is there any way to make this definition now and reuse it later?
      F : Presheaf C _
      F = record
        { F-ob = λ c → ⟨F⟅ c ⟆⟩ , trunc
        ; F-hom = restrict
        ; F-id = funExt restrictId
        ; F-seq = λ f g → funExt (restrictRestrict f g)
        }
      in
      {c : ob} →
      (cover : ⟨ covers c ⟩) →
      let cov = str (covers c) cover in
      CompatibleFamily F cov →
      ⟨F⟅ c ⟆⟩
    restrictAmalgamate :
      let
      F : Presheaf C _
      F = record
        { F-ob = λ c → ⟨F⟅ c ⟆⟩ , trunc
        ; F-hom = restrict
        ; F-id = funExt restrictId
        ; F-seq = λ f g → funExt (restrictRestrict f g)
        }
      in
      {c : ob} →
      (cover : ⟨ covers c ⟩) →
      let cov = str (covers c) cover in
      (fam : CompatibleFamily F cov) →
      (patch : ⟨ cov ⟩) →
      restrict (patchArr cov patch) (amalgamate cover fam) ≡ fst fam patch

  F : Presheaf C (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓcov) ℓpat) ℓP)
  Functor.F-ob F c = ⟨F⟅ c ⟆⟩ , trunc
  Functor.F-hom F = restrict
  Functor.F-id F = funExt restrictId
  Functor.F-seq F f g = funExt (restrictRestrict f g)

  isSheafF : ⟨ amalgamationProperty J F ⟩
  isSheafF c cover = isEmbedding×isSurjection→isEquiv
    ( injEmbedding
        (isSetCompatibleFamily F cov)
        (λ {x} {y} x~y → sep cover x y (funExt⁻ (cong fst x~y)))
    , λ fam →
        ∣ amalgamate cover fam
        , Σ≡Prop
            (str ∘ isCompatibleFamily F cov)
            (funExt (restrictAmalgamate cover fam)) ∣₁ )
    where
    cov = str (covers c) cover


module UniversalProperty
  {ℓ ℓ' ℓcov ℓpat : Level}
  {C : Category ℓ ℓ'}
  (J : Coverage C ℓcov ℓpat)
  where

  open Category C hiding (_∘_)
  open Coverage J

  -- We now assume P to have this level to ensure that F has the same level as P.
  ℓP = ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓcov ℓpat))

  module _
    (P : Presheaf C ℓP)
    where

    open Sheafification J P
    open NatTrans
    open Functor

    η : P ⇒ F
    N-ob η c = η⟦_⟧
    N-hom η f = funExt (ηNatural f)

    module _
      (G : Presheaf C ℓP)
      (isSheafG : ⟨ amalgamationProperty J G ⟩)
      (α : P ⇒ G)
      where

      private

        ν : {c : ob} → ⟨ F ⟅ c ⟆ ⟩ → ⟨ G ⟅ c ⟆ ⟩

        ν (trunc x y p q i j) = str (G ⟅ _ ⟆) _ _ (cong ν p) (cong ν q) i j
        ν (restrict {c} {d} f x) = (G ⟪ f ⟫) (ν x)
        ν (restrictId x i) = funExt⁻ (F-id G) (ν x) i
        ν (restrictRestrict {c} {d} {e} f g x i) = funExt⁻ (F-seq G f g) (ν x) i
        ν η⟦ x ⟧ = (α ⟦ _ ⟧) x
        ν (ηNatural f x i) = funExt⁻ (N-hom α f) x i

        ν (sep cover x y x~y i) =
          isEmbedding→Inj (isEquiv→isEmbedding (isSheafG _ cover))
            (ν x)
            (ν y)
            (Σ≡Prop
              (λ fam → str (isCompatibleFamily G cov fam))
              -- Can't use cong here, to keep termination checker happy.
              (funExt λ patch j → ν (x~y patch j)))
            i
          where
          cov = str (covers _) cover

        ν (amalgamate cover (fam , compat)) =
          fst (fst (equiv-proof (isSheafG _ cover) fam'))
          where
          cov = str (covers _) cover
          -- We have to push forward fam along the natural transformation ν that we are just defining.
          fam' : CompatibleFamily G cov
          fam' =
            (λ i → ν (fam i)) ,
            λ i j d f g diamond → cong ν (compat i j d f g diamond)

        ν (restrictAmalgamate cover (fam , compat) patch i) =
          fst (snd (fst (equiv-proof (isSheafG _ cover) fam')) i) patch
          where
          cov = str (covers _) cover
          fam' : CompatibleFamily G cov
          fam' =
            (λ i → ν (fam i)) ,
            λ i j d f g diamond → cong ν (compat i j d f g diamond)

      inducedMap : F ⇒ G
      N-ob inducedMap c = ν
      N-hom inducedMap f = refl
