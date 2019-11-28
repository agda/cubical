{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Ints.QuoInt.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.Ints.QuoInt.Base
  renaming (_+ℤ_ to _+_)
open import Cubical.Data.Nat
  hiding (+-comm; +-zero; _+_)

+-pos-0 : ∀ a → pos 0 + a ≡ a
+-pos-0 (pos zero) = refl
+-pos-0 (pos (suc n)) = cong sucℤ (+-pos-0 (pos n))
+-pos-0 (neg zero) = posneg
+-pos-0 (neg (suc n)) = cong predℤ (+-pos-0 (neg n))
+-pos-0 (posneg i) j = posneg (i ∧ j)

+-neg-0 : ∀ a → neg 0 + a ≡ a
+-neg-0 (neg zero) = refl
+-neg-0 (neg (suc n)) = cong predℤ (+-neg-0 (neg n))
+-neg-0 (pos zero) = sym posneg
+-neg-0 (pos (suc n)) = cong sucℤ (+-neg-0 (pos n))
+-neg-0 (posneg i) j = posneg (i ∨ ~ j)

+-pos-suc : ∀ a b → sucℤ (pos b + a) ≡ (pos (suc b) + a)
+-pos-suc (pos zero) b = refl
+-pos-suc (pos (suc n)) b = cong sucℤ (+-pos-suc (pos n) b)
+-pos-suc (neg zero) b = refl
+-pos-suc (posneg i) b = refl
+-pos-suc (neg (suc n)) b =
  sucPredℤ (pos b + neg n) ∙∙
  sym (predSucℤ (pos b + neg n)) ∙∙
  cong predℤ (+-pos-suc (neg n) b)
  -- the following hcomp does not termination-check:
  -- hcomp (λ j → λ
  --  { (i = i0) → sucPredℤ (pos b + neg n) (~ j)
  --  ; (i = i1) → {!predℤ ((+-pos-suc (neg n) b) j)!}
  --  }) (predSucℤ (pos b + neg n) (~ i))

+-neg-pred : ∀ a b → predℤ (neg b + a) ≡ (neg (suc b) + a)
+-neg-pred (pos zero) b = refl
+-neg-pred (neg zero) b = refl
+-neg-pred (neg (suc n)) b = cong predℤ (+-neg-pred (neg n) b)
+-neg-pred (posneg i) b = refl
+-neg-pred (pos (suc n)) b =
  predSucℤ (neg b + pos n) ∙∙
  sym (sucPredℤ (neg b + pos n)) ∙∙
  cong sucℤ (+-neg-pred (pos n) b)

+-comm : ∀ a b → a + b ≡ b + a
+-comm a (pos zero) = sym (+-pos-0 a)
+-comm a (neg zero) = sym (+-neg-0 a)
+-comm a (pos (suc b)) = cong sucℤ (+-comm a (pos b)) ∙ +-pos-suc a b
+-comm a (neg (suc b)) = cong predℤ (+-comm a (neg b)) ∙ +-neg-pred a b
+-comm a (posneg i) = lemma a i
  where
  -- get some help from:
  -- https://www.codewars.com/kata/reviews/5c878e3ef1abb10001e32eb1/groups/5cca3f9e840f4b0001d8ac98
  lemma : ∀ a → (λ i → (a + posneg i) ≡ (posneg i + a))
          [ sym (+-pos-0 a) ≡ sym (+-neg-0 a) ]
  lemma (pos zero) i j = posneg (i ∧ j)
  lemma (pos (suc n)) i = cong sucℤ (lemma (pos n) i)
  lemma (neg zero) i j = posneg (i ∨ ~ j)
  lemma (neg (suc n)) i = cong predℤ (lemma (neg n) i)
  lemma (posneg i) j k = posneg ((i ∧ ~ k) ∨ (i ∧ j) ∨ (j ∧ k))

