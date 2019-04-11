{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.ListedFiniteSet.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Everything

open import Cubical.HITs.ListedFiniteSet.Base

private
  variable
    A : Type₀

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
