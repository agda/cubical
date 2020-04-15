{-# OPTIONS --cubical --safe #-}

module Cubical.Categories.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category

module _ ℓ where
  SET : Precategory (ℓ-suc ℓ) ℓ
  SET .ob = Σ (Type ℓ) isSet
  SET .hom (A , _) (B , _) = A → B
  SET .idn _  = λ x → x
  SET .seq f g = λ x → g (f x)
  SET .seq-λ f = refl
  SET .seq-ρ f = refl
  SET .seq-α f g h = refl

module _ {ℓ} where
  isSetExpIdeal : {A B : Type ℓ} → isSet B → isSet (A → B)
  isSetExpIdeal B/set = isSetΠ λ _ → B/set

  isSetLift : {A : Type ℓ} → isSet A → isSet (Lift {ℓ} {ℓ-suc ℓ} A)
  isSetLift = isOfHLevelLift 2

  instance
    SET-category : isCategory (SET ℓ)
    SET-category .homIsSet {_} {B , B/set} = isSetExpIdeal B/set
