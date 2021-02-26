{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Equivalence.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open Precategory
open Functor

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

-- Definition

record isEquivalence {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'}
                     (func : Functor C D) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field
    invFunc : Functor D C

    η : 𝟙⟨ C ⟩ ≅ᶜ invFunc ∘F func
    ε : func ∘F invFunc ≅ᶜ 𝟙⟨ D ⟩

record _≃ᶜ_ (C : Precategory ℓC ℓC') (D : Precategory ℓD ℓD') : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field
    func : Functor C D
    isEquiv : isEquivalence func

