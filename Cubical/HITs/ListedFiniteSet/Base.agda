{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.ListedFiniteSet.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Everything

private
  variable
    A : Type₀

infixr 20 _∷_
infix 30 _∈_


data LFType (A : Type₀) : Type₀ where
  []    : LFType A
  _∷_   : (x : A) → (xs : LFType A) → LFType A
  dup   : ∀ x xs   → x ∷ x ∷ xs ≡ x ∷ xs
  comm  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isType (LFType A)


-- Membership.
--
-- Doing some proofs with equational reasoning adds an extra "_∙ refl"
-- at the end.
-- We might want to avoid it, or come up with a more clever equational reasoning.
_∈_ : A → LFType A → hProp
z ∈ []                  = ⊥
z ∈ (y ∷ xs)            = (z ≡ₚ y) ⊔ (z ∈ xs)
z ∈ dup x xs i          = proof i
  where
    -- proof : z ∈ (x ∷ x ∷ xs) ≡ z ∈ (x ∷ xs)
    proof = z ≡ₚ x  ⊔ (z ≡ₚ x ⊔ z ∈ xs) ≡⟨ ⊔-assoc (z ≡ₚ x) (z ≡ₚ x) (z ∈ xs) ⟩
            (z ≡ₚ x ⊔ z ≡ₚ x) ⊔ z ∈ xs  ≡⟨ cong (_⊔ (z ∈ xs)) (⊔-idem (z ≡ₚ x)) ⟩
            z ≡ₚ x            ⊔ z ∈ xs  ∎
z ∈ comm x y xs i       = proof i
  where
    -- proof : z ∈ (x ∷ y ∷ xs) ≡ z ∈ (y ∷ x ∷ xs)
    proof = z ≡ₚ x  ⊔ (z ≡ₚ y ⊔ z ∈ xs) ≡⟨ ⊔-assoc (z ≡ₚ x) (z ≡ₚ y) (z ∈ xs) ⟩
            (z ≡ₚ x ⊔ z ≡ₚ y) ⊔ z ∈ xs  ≡⟨ cong (_⊔ (z ∈ xs)) (⊔-comm (z ≡ₚ x) (z ≡ₚ y)) ⟩
            (z ≡ₚ y ⊔ z ≡ₚ x) ⊔ z ∈ xs  ≡⟨ sym (⊔-assoc (z ≡ₚ y) (z ≡ₚ x) (z ∈ xs)) ⟩
            z ≡ₚ y  ⊔ (z ≡ₚ x ⊔ z ∈ xs) ∎

x ∈ trunc xs ys p q i j = isTypeHProp (x ∈ xs) (x ∈ ys) (cong (x ∈_) p) (cong (x ∈_) q) i j
