{-# OPTIONS --cubical --rewriting #-}
module Cubical.HITs.S1.Rewrite where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.Int.Rewrite

open import Cubical.HITs.S1

-- This proof currently relies on rewriting hcomp with empty systems in Int to the base
windingIntLoop : (n : Int) → winding (intLoop n) ≡ n
windingIntLoop (pos zero)       = refl
windingIntLoop (pos (suc n))    = λ i → sucInt (windingIntLoop (pos n) i)
windingIntLoop (negsuc zero)    = refl
windingIntLoop (negsuc (suc n)) = λ i → predInt (windingIntLoop (negsuc n) i)

ΩS¹≡Int : ΩS¹ ≡ Int
ΩS¹≡Int = isoToPath winding (decode base) windingIntLoop (decodeEncode base)
