{-

The Essential Image of Functor

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.EssentialImage where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.FullSubcategory

private
  variable
    ℓC ℓC' ℓD ℓD' : Level


module _
  {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (F : Functor C D) where

  open Category
  open Functor


  isInEssentialImage : D .ob → Type (ℓ-max ℓC ℓD')
  isInEssentialImage d = ∃[ c ∈ C .ob ] CatIso D (F .F-ob c) d

  isPropIsInEssentialImage : (d : D .ob) → isProp (isInEssentialImage d)
  isPropIsInEssentialImage _ = squash₁


  -- The Essential Image
  EssentialImage : Category (ℓ-max ℓC (ℓ-max ℓD ℓD')) ℓD'
  EssentialImage = FullSubcategory D isInEssentialImage


  ToEssentialImage : Functor C EssentialImage
  ToEssentialImage .F-ob c = F .F-ob c , ∣ c , idCatIso ∣₁
  ToEssentialImage .F-hom = F .F-hom
  ToEssentialImage .F-id = F .F-id
  ToEssentialImage .F-seq = F .F-seq

  FromEssentialImage : Functor EssentialImage D
  FromEssentialImage = FullInclusion D isInEssentialImage

  CompEssentialImage : funcComp FromEssentialImage ToEssentialImage ≡ F
  CompEssentialImage = Functor≡ (λ _ → refl) (λ _ → refl)


  isEssentiallySurjToEssentialImage : isEssentiallySurj ToEssentialImage
  isEssentiallySurjToEssentialImage (d , p) = PropTrunc.map (λ (c , f) → c , Incl-Iso-inv _ _ _ _ f) p

  isFullyFaithfulFromEssentialImage : isFullyFaithful FromEssentialImage
  isFullyFaithfulFromEssentialImage = isFullyFaithfulIncl D isInEssentialImage


  isFullyFaithfulToEssentialImage : isFullyFaithful F → isFullyFaithful ToEssentialImage
  isFullyFaithfulToEssentialImage fullfaith = fullfaith


  isUnivalentEssentialImage : isUnivalent D → isUnivalent EssentialImage
  isUnivalentEssentialImage = isUnivalentFullSub _ isPropIsInEssentialImage
