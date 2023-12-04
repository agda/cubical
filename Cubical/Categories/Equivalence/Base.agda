{-# OPTIONS --safe #-}
module Cubical.Categories.Equivalence.Base where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open Category
open Functor

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

record WeakInverse {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
                     (func : Functor C D) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field
    invFunc : Functor D C

    η : 𝟙⟨ C ⟩ ≅ᶜ invFunc ∘F func
    ε : func ∘F invFunc ≅ᶜ 𝟙⟨ D ⟩

-- I don't know of a good alternative representation of isEquivalence that
-- avoids truncation in the general case.  If the categories are univalent, then
-- an adjoint equivalence might be enough.
isEquivalence : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
              → (func : Functor C D) → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
isEquivalence func = ∥ WeakInverse func ∥₁

record _≃ᶜ_ (C : Category ℓC ℓC') (D : Category ℓD ℓD') :
               Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  constructor equivᶜ
  field
    func : Functor C D
    isEquiv : isEquivalence func
