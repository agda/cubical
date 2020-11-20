{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.IntAsRawRing where

open import Cubical.Data.Nat hiding (_+_; _·_)
open import Cubical.Data.Int
open import Cubical.Data.Int.Base renaming (Int to ℤ) public

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.RingSolver.RawRing

ℤAsRawRing : RawRing {ℓ-zero}
ℤAsRawRing = rawring ℤ (pos zero) (pos (suc zero)) _+_ _·_ (λ k → (pos zero) - k)
