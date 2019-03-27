{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.ListedFiniteSet.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Everything

private
  variable
    A : Set

infixr 20 _∷_
infix 30 _∈_


data LFSet (A : Set) : Set where
  []    : LFSet A
  _∷_   : (x : A) → (xs : LFSet A) → LFSet A
  dup   : ∀ x xs   → x ∷ x ∷ xs ≡ x ∷ xs
  comm  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isSet (LFSet A)


-- Membership.
--
-- Doing some proofs with equational reasoning adds an extra "_∙ refl"
-- at the end.
-- We might want to avoid it, or come up with a more clever equational reasoning.
_∈_ : A → LFSet A → Ω
z ∈ []                  = ⊥
z ∈ (y ∷ xs)            = (z ≡m y) ⊔ (z ∈ xs)
z ∈ dup x xs i          = proof i
  where
    -- proof : z ∈ (x ∷ x ∷ xs) ≡ z ∈ (x ∷ xs)
    proof = z ≡m x  ⊔ (z ≡m x ⊔ z ∈ xs) ≡⟨ ⊔-assoc (z ≡m x) (z ≡m x) (z ∈ xs) ⟩
            (z ≡m x ⊔ z ≡m x) ⊔ z ∈ xs  ≡⟨ cong (_⊔ (z ∈ xs)) (⊔-idem (z ≡m x)) ⟩
            z ≡m x            ⊔ z ∈ xs  ∎
z ∈ comm x y xs i       = proof i
  where
    -- proof : z ∈ (x ∷ y ∷ xs) ≡ z ∈ (y ∷ x ∷ xs)
    proof = z ≡m x  ⊔ (z ≡m y ⊔ z ∈ xs) ≡⟨ ⊔-assoc (z ≡m x) (z ≡m y) (z ∈ xs) ⟩
            (z ≡m x ⊔ z ≡m y) ⊔ z ∈ xs  ≡⟨ cong (_⊔ (z ∈ xs)) (⊔-comm (z ≡m x) (z ≡m y)) ⟩
            (z ≡m y ⊔ z ≡m x) ⊔ z ∈ xs  ≡⟨ sym (⊔-assoc (z ≡m y) (z ≡m x) (z ∈ xs)) ⟩
            z ≡m y  ⊔ (z ≡m x ⊔ z ∈ xs) ∎

x ∈ trunc xs ys p q i j = isSetHProp (x ∈ xs) (x ∈ ys) (cong (x ∈_) p) (cong (x ∈_) q) i j
