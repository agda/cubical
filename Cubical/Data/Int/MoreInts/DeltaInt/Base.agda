{-# OPTIONS --safe #-}

{-

This file defines integers as equivalence classes of pairs of natural numbers
using a direct & untruncated HIT definition (cf. Data.Int.MoreInts.DiffInt)

and some basic operations, and the zero value:

succ : DeltaInt → DeltaInt
pred : DeltaInt → DeltaInt
zero : {a : ℕ} → DeltaInt

and conversion function for ℕ and Int:

fromℕ : ℕ → DeltaInt
fromℤ : Int → DeltaInt
toℤ : DeltaInt → Int

and a generalized version of cancel:

cancelN : ∀ a b n → a ⊖ b ≡ (n + a) ⊖ n + b

-}

module Cubical.Data.Int.MoreInts.DeltaInt.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (zero)
open import Cubical.Data.Int hiding (abs; _+_) renaming (ℤ to Int)

infixl 5 _⊖_
data DeltaInt : Type₀ where
  _⊖_    : ℕ → ℕ → DeltaInt
  cancel : ∀ a b → a ⊖ b ≡ suc a ⊖ suc b

succ : DeltaInt → DeltaInt
succ (x ⊖ y) = suc x ⊖ y
succ (cancel a b i) = cancel (suc a) b i

pred : DeltaInt → DeltaInt
pred (x ⊖ y) = x ⊖ suc y
pred (cancel a b i) = cancel a (suc b) i

zero : {a : ℕ} → DeltaInt
zero {a} = a ⊖ a

fromℕ : ℕ → DeltaInt
fromℕ n = n ⊖ 0

fromℤ : Int → DeltaInt
fromℤ (pos n) = fromℕ n
fromℤ (negsuc n) = 0 ⊖ suc n

toℤ : DeltaInt → Int
toℤ (x ⊖ y) = x ℕ- y
toℤ (cancel a b i) = a ℕ- b

cancelN : ∀ a b n → a ⊖ b ≡ (n + a) ⊖ n + b
cancelN a b 0 = refl
cancelN a b (suc n) = cancelN a b n ∙ cancel (n + a) (n + b)
