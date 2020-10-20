{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.ListedFiniteSet.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Prod using (_×_; _,_)

open import Cubical.HITs.ListedFiniteSet.Base

private
  variable
    A B : Type₀

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

comm-++-[]
  : ∀ {A} (xs : LFSet A)
  → xs ++ [] ≡ [] ++ xs
comm-++-[] xs = PropElim.f
  (λ xs → xs ++ [] ≡ [] ++ xs)
    refl
    (λ x {xs} ind →
      (x ∷ xs) ++ [] ≡⟨ refl ⟩
      x ∷ (xs ++ []) ≡⟨ cong (x ∷_) ind ⟩
      x ∷ xs ≡⟨ refl ⟩
      [] ++ (x ∷ xs) ∎
  )
  (λ _ → trunc _ _)
  xs

comm-++-∷
  : ∀ {A} (z : A) xs ys
  → xs ++ (z ∷ ys) ≡ (z ∷ xs) ++ ys
comm-++-∷ z xs ys = PropElim.f
  (λ xs → xs ++ (z ∷ ys) ≡ (z ∷ xs) ++ ys)
  refl
  (λ x {xs} ind →
    x ∷ (xs ++ (z ∷ ys)) ≡⟨ cong (x ∷_) ind ⟩
    x ∷ z ∷ (xs ++ ys) ≡⟨ comm x z (xs ++ ys) ⟩
    z ∷ x ∷ (xs ++ ys) ∎
  )
  (λ _ → trunc _ _)
  xs

comm-++ : (xs ys : LFSet A) → xs ++ ys ≡ ys ++ xs
comm-++ xs ys = PropElim.f
  (λ ys → xs ++ ys ≡ ys ++ xs)
  (comm-++-[] xs)
  (λ y {ys} ind →
    xs ++ (y ∷ ys) ≡⟨ comm-++-∷ y xs ys ⟩
    y ∷ (xs ++ ys) ≡⟨ cong (y ∷_) ind ⟩
    y ∷ (ys ++ xs) ≡⟨ refl ⟩
    (y ∷ ys) ++ xs ∎
  )
  (λ _ → trunc _ _)
  ys

idem-++ : (xs : LFSet A) → xs ++ xs ≡ xs
idem-++ = PropElim.f
  (λ xs → xs ++ xs ≡ xs)
  refl
  (λ x {xs} ind →
    (x ∷ xs) ++ (x ∷ xs) ≡⟨ refl ⟩
    x ∷ (xs ++ (x ∷ xs)) ≡⟨ refl ⟩
    x ∷ (xs ++ ((x ∷ []) ++ xs)) ≡⟨ cong (x ∷_) (assoc-++ xs (x ∷ []) xs) ⟩
    x ∷ ((xs ++ (x ∷ [])) ++ xs)
      ≡⟨ cong (λ h → x ∷ (h ++ xs)) (comm-++ xs (x ∷ [])) ⟩
    x ∷ x ∷ (xs ++ xs) ≡⟨ cong (λ ys → x ∷ x ∷ ys) ind ⟩
    x ∷ x ∷ xs ≡⟨ dup x xs ⟩
    x ∷ xs ∎
  )
  (λ xs → trunc (xs ++ xs) xs)

map : (A → B) → LFSet A → LFSet B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs
map f (dup x xs i) = dup (f x) (map f xs) i
map f (comm x y xs i) = comm (f x) (f y) (map f xs) i
map f (trunc xs ys p q i j) = trunc
  (map f xs)
  (map f ys)
  (cong (map f) p)
  (cong (map f) q)
  i j

cart-product : LFSet A → LFSet B → LFSet (A × B)
cart-product [] ys = []
cart-product (x ∷ xs) ys = map (x ,_) ys ++ cart-product xs ys
cart-product (dup x xs i) ys =
  ( map (x ,_) ys ++ (map (x ,_) ys ++ cart-product xs ys)
      ≡⟨ assoc-++ (map (x ,_) ys) (map (x ,_) ys) (cart-product xs ys) ⟩
    (map (x ,_) ys ++ map (x ,_) ys) ++ cart-product xs ys
      ≡⟨ cong (_++ cart-product xs ys) (idem-++ (map (x ,_) ys)) ⟩
    map (x ,_) ys ++ cart-product xs ys
      ∎
  ) i
cart-product (comm x y xs i) ys =
  ( map (x ,_) ys ++ (map (y ,_) ys ++ cart-product xs ys)
      ≡⟨ assoc-++ (map (x ,_) ys) (map (y ,_) ys) (cart-product xs ys) ⟩
    (map (x ,_) ys ++ map (y ,_) ys) ++ cart-product xs ys
      ≡⟨ cong (_++ cart-product xs ys) (comm-++ (map (x ,_) ys) (map (y ,_) ys)) ⟩
    (map (y ,_) ys ++ map (x ,_) ys) ++ cart-product xs ys
      ≡⟨ sym (assoc-++ (map (y ,_) ys) (map (x ,_) ys) (cart-product xs ys)) ⟩
    map (y ,_) ys ++ (map (x ,_) ys ++ cart-product xs ys)
      ∎
  ) i
cart-product (trunc xs xs′ p q i j) ys = trunc
  (cart-product xs ys)
  (cart-product xs′ ys)
  (λ k → cart-product (p k) ys)
  (λ k → cart-product (q k) ys)
  i
  j

disj-union : LFSet A → LFSet B → LFSet (A ⊎ B)
disj-union xs ys = map inl xs ++ map inr ys
