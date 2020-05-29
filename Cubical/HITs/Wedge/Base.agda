{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Wedge.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.HITs.Pushout.Base
open import Cubical.Data.Unit

_⋁_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Type (ℓ-max ℓ ℓ')
_⋁_ (A , ptA) (B , ptB) = Pushout {A = Unit} {B = A} {C = B} (λ _ → ptA) (λ _ → ptB)


-- pointed versions

_⋁∙ₗ_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
A ⋁∙ₗ B = (A ⋁ B) , (inl (snd A))

_⋁∙ᵣ_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
A ⋁∙ᵣ B = (A ⋁ B) , (inr (snd B))

