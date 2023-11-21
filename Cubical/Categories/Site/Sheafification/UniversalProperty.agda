{-# OPTIONS --safe #-}
module Cubical.Categories.Site.Sheafification.UniversalProperty where

-- We prove the universal property of the sheafification,
-- exhibiting it as a left adjoint to the forgetful functor.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_$_; _∘_)
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.FullSubcategory

open import Cubical.Categories.Site.Cover
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Site.Sheaf

open import Cubical.Categories.Site.Sheafification.Base
open import Cubical.Categories.Site.Sheafification.ElimProp


module UniversalProperty
  {ℓ ℓ' ℓcov ℓpat : Level}
  {C : Category ℓ ℓ'}
  (J : Coverage C ℓcov ℓpat)
  where

  -- We assume 'P' to have the following universe level in order to ensure that
  -- the sheafification does not raise the universe level.
  -- This is unfortunately necessary as long as we want to use the general
  -- definition of natural transformations for the maps between presheaves.
  -- (Other than that, the sheafification construction should enjoy the expected
  -- universal property also for 'P' of arbitrary universe level.)
  ℓP = ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓcov ℓpat))

  module _
    (P : Presheaf C ℓP)
    where

    open Category C hiding (_∘_)

    private
      C^ = PresheafCategory C ℓP
      module C^ = Category C^

    open Coverage J
    open Sheafification J P
    open NatTrans
    open Functor

    η : P ⇒ sheafification
    N-ob η c = η⟦⟧
    N-hom η f = funExt (ηNatural f)

    module InducedMap
      (G : Presheaf C ℓP)
      (isSheafG : isSheaf J G)
      (α : P ⇒ G)
      where

{-
           η
        P --> sheafification
         \    .
          \   . inducedMap
         α \  .
            ∨ ∨
              G
-}

      private

        ν : {c : ob} → ⟨ sheafification ⟅ c ⟆ ⟩ → ⟨ G ⟅ c ⟆ ⟩

        ν (trunc x y p q i j) = str (G ⟅ _ ⟆) _ _ (cong ν p) (cong ν q) i j
        ν (restrict f x) = (G ⟪ f ⟫) (ν x)
        ν (restrictId x i) = funExt⁻ (F-id G) (ν x) i
        ν (restrictRestrict {c} {d} {e} f g x i) = funExt⁻ (F-seq G f g) (ν x) i
        ν (η⟦⟧ x) = (α ⟦ _ ⟧) x
        ν (ηNatural f x i) = funExt⁻ (N-hom α f) x i

        ν (sep cover x y x~y i) =
          isSheaf→isSeparated J G isSheafG _ cover
            (ν x)
            (ν y)
            (λ patch → cong ν (x~y patch))
            i
          where
          cov = str (covers _) cover

        ν (amalgamate cover (fam , compat)) =
          fst (fst (equiv-proof (isSheafG _ cover) fam'))
          where
          cov = str (covers _) cover
          -- We have to push forward 'fam' along the natural transformation 'ν' that we are just defining.
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

      inducedMap : sheafification ⇒ G
      N-ob inducedMap c = ν
      N-hom inducedMap f = refl

      inducedMapFits : η C^.⋆ inducedMap ≡ α
      inducedMapFits = makeNatTransPath refl

      module _
        (β : sheafification ⇒ G)
        (βFits : η C^.⋆ β ≡ α)
        where

        open ElimPropAssumptions J P

        private
          B : {c : ob} → ⟨ sheafification ⟅ c ⟆ ⟩ → Type _
          B x = (β ⟦ _ ⟧) x ≡ ν x

          isPropValuedB : isPropValued B
          isPropValuedB = str (G ⟅ _ ⟆) _ _

          onηB : Onη B
          onηB = funExt⁻ (funExt⁻ (cong N-ob βFits) _)

          isLocalB : isLocal B
          isLocalB x cover locallyAgree =
            isSheaf→isSeparated J G isSheafG _ cover
              ((β ⟦ _ ⟧) x)
              (ν x)
              λ patch →
                let f = patchArr (str (covers _) cover) patch in
                (G ⟪ f ⟫) ((β ⟦ _ ⟧) x)                 ≡⟨ sym (cong (_$ x) (N-hom β f)) ⟩
                ((β ⟦ _ ⟧) ((sheafification ⟪ f ⟫) x))  ≡⟨ locallyAgree patch ⟩
                (G ⟪ f ⟫) (ν x)                         ∎

        uniqueness : β ≡ inducedMap
        uniqueness = makeNatTransPath (funExt λ _ → funExt (
          elimProp J P {B = B} isPropValuedB onηB isLocalB))

        -- This alternative proof does not use the 'pullbackStability' of the coverage.
        module _ where private

          isMonotonousB : isMonotonous B
          isMonotonousB f x βx≡νx =
            (β ⟦ _ ⟧) (restrict f x)  ≡⟨ cong (_$ x) (N-hom β f) ⟩
            (G ⟪ f ⟫) ((β ⟦ _ ⟧) x)   ≡⟨ cong (G ⟪ f ⟫) βx≡νx ⟩
            (G ⟪ f ⟫) (ν x)           ∎

          uniqueness' : β ≡ inducedMap
          uniqueness' = makeNatTransPath (funExt λ _ → funExt (
            ElimPropWithMonotonous.elimProp J P
              {B = B}
              isPropValuedB
              onηB
              isLocalB
              isMonotonousB))

    sheafificationIsUniversal :
      isUniversal
        (SheafCategory J ℓP ^op)
        ((C^ [ P ,-]) ∘F FullInclusion C^ (isSheaf J))
        (sheafification , isSheafSheafification)
        η
    sheafificationIsUniversal (G , isSheafG) = record
      { equiv-proof = λ α →
          let open InducedMap G isSheafG α in
            (inducedMap , inducedMapFits)
          , λ (β , βFits) →
              Σ≡Prop
                (λ _ → C^.isSetHom _ _)
                (sym (uniqueness β βFits))
      }
