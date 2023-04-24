{-

The Construction of Rezk Completion

-}
{-# OPTIONS --safe --lossy-unification #-}

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


-- There are two different ways to construct the Rezk completion,
-- one is using the essential image of the Yoneda embbeding,
-- another one is using a higher inductive type
-- (c.f. HoTT Book Chaper 9.9).

-- Yoneda embbeding can give a very simple and quick construction.
-- Unfortunately, this construction increases the universe level.

-- The HIT construction, on the other hand, keeps the universe level,
-- but its proof is a bit long and tedious, still easy though.


{- The Construction by Yoneda Embedding -}

module RezkByYoneda (C : Category ℓ ℓ) where

  YonedaImage : Category (ℓ-suc ℓ) ℓ
  YonedaImage = EssentialImage (YO {C = C})

  isUnivalentYonedaImage : isUnivalent YonedaImage
  isUnivalentYonedaImage = isUnivalentEssentialImage _ isUnivalentPresheafCategory

  ToYonedaImage : Functor C YonedaImage
  ToYonedaImage = ToEssentialImage _

  isWeakEquivalenceToYonedaImage : isWeakEquivalence ToYonedaImage
  isWeakEquivalenceToYonedaImage .fullfaith = isFullyFaithfulToEssentialImage _ isFullyFaithfulYO
  isWeakEquivalenceToYonedaImage .esssurj   = isEssentiallySurjToEssentialImage YO

  isRezkCompletionToYonedaImage : isRezkCompletion ToYonedaImage
  isRezkCompletionToYonedaImage = makeIsRezkCompletion isUnivalentYonedaImage isWeakEquivalenceToYonedaImage


{- The Construction by Higher Inductive Type -}

module RezkByHIT (C : Category ℓ ℓ') where

  -- TODO: Write the HIT construction of Rezk completion here.
