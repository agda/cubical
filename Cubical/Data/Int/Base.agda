{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Int.Base where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

data Int : Type₀ where
  pos    : (n : ℕ) → Int
  negsuc : (n : ℕ) → Int

sucInt : Int → Int
sucInt (pos n)          = pos (suc n)
sucInt (negsuc zero)    = pos zero
sucInt (negsuc (suc n)) = negsuc n

predInt : Int → Int
predInt (pos zero)    = negsuc zero
predInt (pos (suc n)) = pos n
predInt (negsuc n)    = negsuc (suc n)
