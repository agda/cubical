{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Int.Base where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

data Int : Type₀ where
  pos    : (n : ℕ) → Int
  negsuc : (n : ℕ) → Int

neg : (n : ℕ) → Int
neg zero = pos zero
neg (suc n) = negsuc n

sucInt : Int → Int
sucInt (pos n)          = pos (suc n)
sucInt (negsuc zero)    = pos zero
sucInt (negsuc (suc n)) = negsuc n

predInt : Int → Int
predInt (pos zero)    = negsuc zero
predInt (pos (suc n)) = pos n
predInt (negsuc n)    = negsuc (suc n)

-- Natural number and negative integer literals for Int

open import Cubical.Data.Nat.Literals public

instance
  fromNatInt : HasFromNat Int
  fromNatInt = record { Constraint = λ _ → Unit ; fromNat = λ n → pos n }

instance
  fromNegInt : HasFromNeg Int
  fromNegInt = record { Constraint = λ _ → Unit ; fromNeg = λ n → neg n }
