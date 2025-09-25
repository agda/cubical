module Cubical.Functions.Image where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Powerset

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
  imageInclusion = EmbeddingΣProp isPropIsInImage

  restrictToImage : A → Image
  restrictToImage x = (f x) , ∣ x , refl ∣₁

  isSurjectionImageRestriction : isSurjection restrictToImage
  isSurjectionImageRestriction (y , y∈im) =
    PT.rec isPropPropTrunc
           (λ (x , fx≡y)
             → ∣ x , Σ≡Prop isPropIsInImage fx≡y ∣₁)
           y∈im

  imageFactorization : fst imageInclusion ∘ restrictToImage ≡ f
  imageFactorization = refl

{-
  Uniqueness of images.
  Stated in such a way that the two image object can have different universe levels.
-}

module _ {ℓ₀ ℓ₁}
  {Im₀ : Type ℓ₀} (e₀ : A ↠ Im₀) (m₀ : Im₀ ↪ B)
  {Im₁ : Type ℓ₁} (e₁ : A ↠ Im₁) (m₁ : Im₁ ↪ B)
  (p : m₀ .fst ∘ e₀ .fst ≡ m₁ .fst ∘ e₁ .fst)
  where

  private
    helper : (c : Im₀) → fiber (m₁ .fst) (m₀ .fst c)
    helper c =
      PT.rec
        (isEmbedding→hasPropFibers (m₁ .snd) (m₀ .fst c))
        (λ (a , q) → e₁ .fst a , sym (funExt⁻ p a) ∙ cong (m₀ .fst) q)
        (e₀ .snd c)

  imagesCompare : Im₀ → Im₁
  imagesCompare = fst ∘ helper

  imagesEmbeddingComm : (c : Im₀) → m₁ .fst (imagesCompare c) ≡ m₀ .fst c
  imagesEmbeddingComm = snd ∘ helper

  imagesSurjectionComm : (a : A) → imagesCompare (e₀ .fst a) ≡ e₁ .fst a
  imagesSurjectionComm a =
    invIsEq (m₁ .snd _ _) (imagesEmbeddingComm _ ∙ funExt⁻ p a)

module _ {ℓ₀ ℓ₁}
  {Im₀ : Type ℓ₀} (e₀ : A ↠ Im₀) (m₀ : Im₀ ↪ B)
  {Im₁ : Type ℓ₁} (e₁ : A ↠ Im₁) (m₁ : Im₁ ↪ B)
  (p : m₀ .fst ∘ e₀ .fst ≡ m₁ .fst ∘ e₁ .fst)
  where

  imagesIso : Iso Im₀ Im₁
  imagesIso .Iso.fun = imagesCompare e₀ m₀ e₁ m₁ p
  imagesIso .Iso.inv = imagesCompare e₁ m₁ e₀ m₀ (sym p)
  imagesIso .Iso.rightInv c =
    invIsEq (m₁ .snd _ _)
      (imagesEmbeddingComm e₀ m₀ e₁ m₁ p _ ∙ imagesEmbeddingComm e₁ m₁ e₀ m₀ (sym p) c)
  imagesIso .Iso.leftInv c =
    invIsEq (m₀ .snd _ _)
      (imagesEmbeddingComm e₁ m₁ e₀ m₀ (sym p) _ ∙ imagesEmbeddingComm e₀ m₀ e₁ m₁ p c)

  imagesEquiv : Im₀ ≃ Im₁
  imagesEquiv = isoToEquiv imagesIso

{-
  Images of subsets.
  The universe level of domain and codomain is equal, so we can use
  the notion of powerset ℙ - so subsets of a type A : Type ℓ, are
  maps A → hProp ℓ.
-}
module _ {A B : Type ℓ} (f : A → B) where
  isInSubsetImage : ℙ A → B → Type _
  isInSubsetImage U y = ∃[ x ∈ A ] (x ∈ U) × (f x ≡ y)

  SubsetImage : ℙ A → ℙ B
  SubsetImage U y = isInSubsetImage U y , isPropPropTrunc

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

{-
  This is the extension to an 'iff', which is also a general modal fact.
-}
isEmbeddingFromIsEquivToImage : (f : A → B) → isEquiv (restrictToImage f) → isEmbedding f
isEmbeddingFromIsEquivToImage f isEquiv-r = isEmbedding-∘ (snd (imageInclusion f)) (isEquiv→isEmbedding isEquiv-r)
