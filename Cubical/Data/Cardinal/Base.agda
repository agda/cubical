{-

This file contains:

- Treatment of set truncation as cardinality
  as per the HoTT book, section 10.2

-}
{-# OPTIONS --safe #-}
module Cubical.Data.Cardinal.Base where

open import Cubical.HITs.SetTruncation as ∥₂
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' : Level

-- First, we define a cardinal as the set truncation of Set
Card : Type (ℓ-suc ℓ)
Card {ℓ} = ∥ hSet ℓ ∥₂

-- Verify that it's a set
isSetCard : isSet (Card {ℓ})
isSetCard = isSetSetTrunc

-- Set truncation of a set is its cardinality
card : hSet ℓ → Card {ℓ}
card = ∣_∣₂

-- Some special cardinalities
𝟘 : Card {ℓ}
𝟘 = card (⊥* , isProp→isSet isProp⊥*)

𝟙 : Card {ℓ}
𝟙 = card (Unit* , isSetUnit*)

-- Now we define some arithmetic
_+_ : Card {ℓ} → Card {ℓ'} → Card {ℓ-max ℓ ℓ'}
_+_ = ∥₂.rec2 isSetCard λ (A , isSetA) (B , isSetB)
                        → card ((A ⊎ B) , isSet⊎ isSetA isSetB)

_·_ : Card {ℓ} → Card {ℓ'} → Card {ℓ-max ℓ ℓ'}
_·_ = ∥₂.rec2 isSetCard λ (A , isSetA) (B , isSetB)
                        → card ((A × B) , isSet× isSetA isSetB)

_^_ : Card {ℓ} → Card {ℓ'} → Card {ℓ-max ℓ ℓ'}
_^_ = ∥₂.rec2 isSetCard λ (A , isSetA) (B , _)
                        → card ((B → A) , isSet→ isSetA)
