-- This is the preferred version of the integers in the library. Other
-- versions can be found in the MoreInts directory.
{-# OPTIONS --safe #-}
module Cubical.Data.Int.Base where

open import Cubical.Core.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Nat hiding (_+_ ; _·_) renaming (isEven to isEvenℕ ; isOdd to isOddℕ)

infix  8 -_
infixl 7 _·_
infixl 6 _+_ _-_

data ℤ : Type₀ where
  pos    : (n : ℕ) → ℤ
  negsuc : (n : ℕ) → ℤ

neg : (n : ℕ) → ℤ
neg zero    = pos zero
neg (suc n) = negsuc n

sucℤ : ℤ → ℤ
sucℤ (pos n)          = pos (suc n)
sucℤ (negsuc zero)    = pos zero
sucℤ (negsuc (suc n)) = negsuc n

predℤ : ℤ → ℤ
predℤ (pos zero)    = negsuc zero
predℤ (pos (suc n)) = pos n
predℤ (negsuc n)    = negsuc (suc n)

isEven : ℤ → Bool
isEven (pos n) = isEvenℕ n
isEven (negsuc n) = isOddℕ n

isOdd : ℤ → Bool
isOdd (pos n) = isOddℕ n
isOdd (negsuc n) = isEvenℕ n

abs : ℤ → ℕ
abs (pos n) = n
abs (negsuc n) = suc n

_ℕ-_ : ℕ → ℕ → ℤ
a ℕ- 0 = pos a
0 ℕ- suc b = negsuc b
suc a ℕ- suc b = a ℕ- b

_+pos_ : ℤ → ℕ  → ℤ
z +pos 0 = z
z +pos (suc n) = sucℤ (z +pos n)

_+negsuc_ : ℤ → ℕ → ℤ
z +negsuc 0 = predℤ z
z +negsuc (suc n) = predℤ (z +negsuc n)

_+_ : ℤ → ℤ → ℤ
m + pos n = m +pos n
m + negsuc n = m +negsuc n

-_ : ℤ → ℤ
- pos zero = pos zero
- pos (suc n) = negsuc n
- negsuc n = pos (suc n)

_-_ : ℤ → ℤ → ℤ
m - n = m + (- n)

_·_ : ℤ → ℤ → ℤ
pos zero · m = pos zero
pos (suc n) · m = m + pos n · m
negsuc zero · m = - m
negsuc (suc n) · m = - m + negsuc n · m

-- Natural number and negative integer literals for ℤ

open import Cubical.Data.Nat.Literals public

instance
  fromNatℤ : HasFromNat ℤ
  fromNatℤ = record { Constraint = λ _ → Unit ; fromNat = λ n → pos n }

instance
  fromNegℤ : HasFromNeg ℤ
  fromNegℤ = record { Constraint = λ _ → Unit ; fromNeg = λ n → neg n }
