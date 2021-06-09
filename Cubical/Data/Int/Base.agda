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

data Int : Type₀ where
  pos    : (n : ℕ) → Int
  negsuc : (n : ℕ) → Int

neg : (n : ℕ) → Int
neg zero    = pos zero
neg (suc n) = negsuc n

sucInt : Int → Int
sucInt (pos n)          = pos (suc n)
sucInt (negsuc zero)    = pos zero
sucInt (negsuc (suc n)) = negsuc n

predInt : Int → Int
predInt (pos zero)    = negsuc zero
predInt (pos (suc n)) = pos n
predInt (negsuc n)    = negsuc (suc n)

isEven : Int → Bool
isEven (pos n) = isEvenℕ n
isEven (negsuc n) = isOddℕ n

isOdd : Int → Bool
isOdd (pos n) = isOddℕ n
isOdd (negsuc n) = isEvenℕ n

abs : Int → ℕ
abs (pos n) = n
abs (negsuc n) = suc n

_ℕ-_ : ℕ → ℕ → Int
a ℕ- 0 = pos a
0 ℕ- suc b = negsuc b
suc a ℕ- suc b = a ℕ- b

_+pos_ : Int → ℕ  → Int
z +pos 0 = z
z +pos (suc n) = sucInt (z +pos n)

_+negsuc_ : Int → ℕ → Int
z +negsuc 0 = predInt z
z +negsuc (suc n) = predInt (z +negsuc n)

_+_ : Int → Int → Int
m + pos n = m +pos n
m + negsuc n = m +negsuc n

-_ : Int → Int
- pos zero = pos zero
- pos (suc n) = negsuc n
- negsuc n = pos (suc n)

_-_ : Int → Int → Int
m - n = m + (- n)

_·_ : Int → Int → Int
pos zero · m = pos zero
pos (suc n) · m = m + pos n · m
negsuc zero · m = - m
negsuc (suc n) · m = - m + negsuc n · m

-- Natural number and negative integer literals for Int

open import Cubical.Data.Nat.Literals public

instance
  fromNatInt : HasFromNat Int
  fromNatInt = record { Constraint = λ _ → Unit ; fromNat = λ n → pos n }

instance
  fromNegInt : HasFromNeg Int
  fromNegInt = record { Constraint = λ _ → Unit ; fromNeg = λ n → neg n }
