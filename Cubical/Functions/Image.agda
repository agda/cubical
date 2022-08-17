{-# OPTIONS --safe #-}
module Cubical.Functions.Image where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma

private variable
  ℓ ℓ' : Level
  A B : Type ℓ

module _ (f : A → B) where
  isInImage : B → Type _
  isInImage y = ∃[ x ∈ A ] f x ≡ y

  isPropIsInImage : (x : B) → isProp (isInImage x)
  isPropIsInImage x = isPropPropTrunc

  Image : Type _
  Image = Σ[ y ∈ B ] isInImage y

  imageInclusion : Image ↪ B
  imageInclusion = fst ,
    hasPropFibers→isEmbedding {f = fst}
      λ y → isOfHLevelRetractFromIso 1 (ϕ y) isPropPropTrunc
      where
        ϕ : (y : B) → Iso _ _
        ϕ y = invIso (fiberProjIso B isInImage y)

  restrictToImage : A → Image
  restrictToImage x = (f x) , ∣ x , refl ∣₁

  isSurjectionImageRestriction : isSurjection restrictToImage
  isSurjectionImageRestriction (y , y∈im) =
    PT.rec isPropPropTrunc
           (λ (x , fx≡y)
             → ∣ x , Σ≡Prop isPropIsInImage fx≡y ∣₁)
           y∈im



{-
  The following is also true for a general modality in place of ∥_∥₁,
  i.e. the modal-connected factor of a modal map is an equivalence.
-}
module _ (f : A ↪ B) where
  private
    f' = fst f
    r = restrictToImage f'
    propFibers = isEmbedding→hasPropFibers (snd f)

    restrictionHasSameFibers : ((y , y∈im) : Image f') →  fiber r (y , y∈im) ≃ fiber f' y
    restrictionHasSameFibers (y , y∈im) =
            _ ,
           totalEquiv (λ x → r x ≡ (y , y∈im)) (λ x → fst (r x) ≡ y)
                      (λ x → cong fst )
                      λ x → snd (imageInclusion f') (r x) (y , y∈im)

  isEquivEmbeddingOntoImage : isEquiv (restrictToImage (fst f))
  isEquivEmbeddingOntoImage =
    isEmbedding×isSurjection→isEquiv
      (hasPropFibers→isEmbedding
        (λ y → isOfHLevelRetractFromIso 1
                 (equivToIso (restrictionHasSameFibers y))
                 (isEmbedding→hasPropFibers (snd f) (fst y)) ) ,
      (isSurjectionImageRestriction (fst f)))
