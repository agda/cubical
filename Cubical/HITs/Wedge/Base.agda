{-# OPTIONS --safe #-}
module Cubical.HITs.Wedge.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.HITs.Pushout.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

_⋁_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Type (ℓ-max ℓ ℓ')
_⋁_ (A , ptA) (B , ptB) = Pushout {A = Unit} {B = A} {C = B} (λ _ → ptA) (λ _ → ptB)


-- pointed versions

_⋁∙ₗ_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
A ⋁∙ₗ B = (A ⋁ B) , (inl (snd A))

_⋁∙ᵣ_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
A ⋁∙ᵣ B = (A ⋁ B) , (inr (snd B))

-- Wedge sum of Units is contractible
isContr-Unit⋁Unit : isContr ((Unit , tt) ⋁ (Unit , tt))
fst isContr-Unit⋁Unit = inl tt
snd isContr-Unit⋁Unit (inl tt) = refl
snd isContr-Unit⋁Unit (inr tt) = push tt
snd isContr-Unit⋁Unit (push tt i) j = push tt (i ∧ j)

⋁-fun : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
      → A ⋁ B → typ A × typ B
⋁-fun {B = B} (inl x) = x , pt B
⋁-fun {A = A} (inr x) = pt A , x
⋁-fun {A = A} {B = B} (push a i) = pt A , pt B
