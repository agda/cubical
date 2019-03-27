{-# OPTIONS --cubical --safe #-}
module ListedFiniteSets where


open import Cubical.Core.Everything
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Everything

variable
  A : Set

infixr 20 _∷_

data LFSet (A : Set) : Set where
  []    : LFSet A
  _∷_   : (x : A) → (xs : LFSet A) → LFSet A
  dup   : ∀ x xs   → x ∷ x ∷ xs ≡ x ∷ xs
  comm  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isSet (LFSet A)



_++_ : ∀ (xs ys : LFSet A) → LFSet A
[]                  ++ ys = ys
(x ∷ xs)            ++ ys = x ∷ (xs ++ ys)
---------------------------------------------
dup x xs i          ++ ys = proof i
   where
     proof :
     -- Need:  (x ∷ x ∷ xs) ++ ys ≡ (x ∷ xs) ++ ys
     -- which reduces to:
               x ∷ x ∷ (xs ++ ys) ≡ x ∷ (xs ++ ys)
     proof = dup x (xs ++ ys)
comm x y xs i       ++ ys = comm x y (xs ++ ys) i
trunc xs zs p q i j ++ ys
  = trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j




assoc-++ : ∀ (xs : LFSet A) ys zs → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc-++ []       ys zs = refl
assoc-++ (x ∷ xs) ys zs
  = cong (x ∷_) (assoc-++ xs ys zs)
------------------------------------
assoc-++ (dup x xs i) ys zs j
  = dup x (assoc-++ xs ys zs j) i
assoc-++ (comm x y xs i) ys zs j
  = comm x y (assoc-++ xs ys zs j) i
assoc-++ (trunc xs xs' p q i k) ys zs j
  = trunc (assoc-++ xs ys zs j) (assoc-++ xs' ys zs j)
          (cong (\ xs -> assoc-++ xs ys zs j) p) (cong (\ xs -> assoc-++ xs ys zs j) q) i k



infix 30 _≡m_  _∈_

_≡m_ : ∀ (x y : A) → Ω
_≡m_ x y = ∥ x ≡ y ∥ , propTruncIsProp


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
