{-# OPTIONS --safe #-}
module Cubical.Functions.Image where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Logic
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

  image : Type _
  image = Σ[ y ∈ B ] isInImage y

  imageInclusion : image ↪ B
  imageInclusion = fst ,
    hasPropFibers→isEmbedding {f = fst}
      λ y → isOfHLevelRetractFromIso 1 (ϕ y) isPropPropTrunc
      where
        ϕ : (y : B) → Iso _ _
        ϕ y = invIso (fiberProjIso B isInImage y)

  restrictToImage : A → image
  restrictToImage x = (f x) , ∣ x , refl ∣₁

  isSurjectionImageRestriction : isSurjection restrictToImage
  isSurjectionImageRestriction (y , y∈im) =
    PT.rec isPropPropTrunc
           (λ (x , fx≡y)
             → ∣ x , Σ≡Prop (λ _ → isPropPropTrunc) fx≡y ∣₁)
           y∈im
