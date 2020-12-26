{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category

open Precategory

module _ ℓ where
  SET : Precategory (ℓ-suc ℓ) ℓ
  SET .ob = Σ (Type ℓ) isSet
  SET .Hom[_,_] (A , _) (B , _) = A → B
  SET .id _  = λ x → x
  SET ._⋆_ f g = λ x → g (f x)
  SET .⋆IdL f = refl
  SET .⋆IdR f = refl
  SET .⋆Assoc f g h = refl

module _ {ℓ} where
  isSetExpIdeal : {A B : Type ℓ} → isSet B → isSet (A → B)
  isSetExpIdeal B/set = isSetΠ λ _ → B/set

  isSetLift : {A : Type ℓ} → isSet A → isSet (Lift {ℓ} {ℓ-suc ℓ} A)
  isSetLift = isOfHLevelLift 2

  instance
    SET-category : isCategory (SET ℓ)
    SET-category .isSetHom {_} {B , B/set} = isSetExpIdeal B/set
