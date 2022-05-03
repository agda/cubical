{-# OPTIONS --safe #-}
module Cubical.HITs.ListedFiniteSet.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)

open import Cubical.Functions.Logic

private
  variable
    ℓ : Level
    A B : Type ℓ

infixr 20 _∷_
-- infix 30 _∈_
infixr 5 _++_

data LFSet (A : Type ℓ) : Type ℓ where
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
_∈_ : {A : Type ℓ} → A → LFSet A → hProp ℓ
z ∈ []                  = Lift ⊥.⊥ , isOfHLevelLift 1 isProp⊥
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
x ∈ trunc xs ys p q i j = isSetHProp (x ∈ xs) (x ∈ ys) (cong (x ∈_) p) (cong (x ∈_) q) i j

module Elim {ℓ}
  {B : LFSet A → Type ℓ}
  ([]* : B [])
  (_∷*_ : (x : A) {xs : LFSet A} → B xs → B (x ∷ xs))
  (comm* : (x y : A) {xs : LFSet A} (b : B xs)
    → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
  (dup* : (x : A) {xs : LFSet A} (b : B xs)
    → PathP (λ i → B (dup x xs i)) (x ∷* (x ∷* b)) (x ∷* b))
  (trunc* : (xs : LFSet A) → isSet (B xs)) where

  f : ∀ x → B x
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (dup x xs i) = dup* x (f xs) i
  f (comm x y xs i) = comm* x y (f xs) i
  f (trunc x y p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc*
      (f x) (f y)
      (λ i → f (p i)) (λ i → f (q i))
      (trunc x y p q) i j

module Rec {ℓ} {B : Type ℓ}
  ([]* : B)
  (_∷*_ : (x : A) → B → B)
  (comm* : (x y : A) (xs : B) → (x ∷* (y ∷* xs)) ≡ (y ∷* (x ∷* xs)))
  (dup* : (x : A) (b : B) → (x ∷* (x ∷* b)) ≡ (x ∷* b))
  (trunc* : isSet B) where

  f : LFSet A → B
  f =
    Elim.f
      []* (λ x xs → x ∷* xs)
      (λ x y b → comm* x y b) (λ x b → dup* x b)
      λ _ → trunc*

module PropElim {ℓ}
  {B : LFSet A → Type ℓ}
  ([]* : B []) (_∷*_ : (x : A) {xs : LFSet A} → B xs → B (x ∷ xs))
  (trunc* : (xs : LFSet A) → isProp (B xs)) where

  f : ∀ x → B x
  f =
    Elim.f
      []* _∷*_
      (λ _ _ _ → isOfHLevel→isOfHLevelDep 1 trunc* _ _ _)
      (λ _ _ → isOfHLevel→isOfHLevelDep 1 trunc* _ _ _)
      λ xs → isProp→isSet (trunc* xs)

_++_ : ∀ (xs ys : LFSet A) → LFSet A
[]                  ++ ys = ys
(x ∷ xs)            ++ ys = x ∷ (xs ++ ys)
dup x xs i          ++ ys = dup x (xs ++ ys) i
comm x y xs i       ++ ys = comm x y (xs ++ ys) i
trunc xs zs p q i j ++ ys =
  trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j

map : (A → B) → LFSet A → LFSet B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs
map f (dup x xs i) = dup (f x) (map f xs) i
map f (comm x y xs i) = comm (f x) (f y) (map f xs) i
map f (trunc xs ys p q i j) =
  trunc (map f xs) (map f ys) (cong (map f) p) (cong (map f) q) i j

disj-union : LFSet A → LFSet B → LFSet (A ⊎ B)
disj-union xs ys = map ⊎.inl xs ++ map ⊎.inr ys
