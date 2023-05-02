
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.TwistedArrow where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.Elements
open Covariant
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓ ℓ' : Level
TwistedArrowCategory : (C : Category ℓ ℓ') → Category (ℓ-max ℓ ℓ') ℓ'
TwistedArrowCategory C = ∫ HomFunctor C

TwistedEnds : (C : Category ℓ ℓ') → Functor (TwistedArrowCategory C) (C ^op ×C C)
TwistedEnds C = ForgetElements (HomFunctor C)

TwistedDom : (C : Category ℓ ℓ') → Functor ((TwistedArrowCategory C) ^op) C
TwistedDom C = ((Fst (C ^op) C) ^opF) ∘F (ForgetElements (HomFunctor C) ^opF)

TwistedCod : (C : Category ℓ ℓ') → Functor (TwistedArrowCategory C) C
TwistedCod C = (Snd (C ^op) C) ∘F ForgetElements (HomFunctor C)
