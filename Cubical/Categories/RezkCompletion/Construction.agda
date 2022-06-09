{-

The Construction of Rezk Completion

-}
{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Categories.RezkCompletion.Construction where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Constructions.EssentialImage
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Yoneda

open import Cubical.Categories.RezkCompletion.Base

private
  variable
    ℓ ℓ' : Level

open isWeakEquivalence



module RezkByYoneda (ℓS : Level)(C : Category ℓ ℓ) where

  YonedaImage : Category (ℓ-suc ℓ) ℓ
  YonedaImage = EssentialImage (YO {C = C})

  isUnivalentYonedaImage : isUnivalent YonedaImage
  isUnivalentYonedaImage = isUnivalentEssentialImage _ isUnivalentPreShv

  ToYonedaImage : Functor C YonedaImage
  ToYonedaImage = ToEssentialImage _

  isWeakEquivalenceToYonedaImage : isWeakEquivalence ToYonedaImage
  isWeakEquivalenceToYonedaImage .fullfaith = {!!}
  isWeakEquivalenceToYonedaImage .esssurj   = isEssentiallySurjToEssentialImage YO

  isRezkCompletionToYonedaImage : isRezkCompletion ToYonedaImage
  isRezkCompletionToYonedaImage = makeIsRezkCompletion isUnivalentYonedaImage isWeakEquivalenceToYonedaImage
