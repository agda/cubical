{-# OPTIONS --safe #-}
module Cubical.Algebra.IntegerMatrix.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.SumFin

private
  variable
    m n : ℕ

-- Basic Definitions

Vector : ℕ → Type
Vector n = Fin n → ℤ

Matrix : ℕ → ℕ → Type
Matrix m n = Fin m → Fin n → ℤ

isSetVector : isSet (Vector n)
isSetVector = isSetΠ (λ _ → isSetℤ)

isSetMatrix : isSet (Matrix m n)
isSetMatrix = isSetΠ2 (λ _ _ → isSetℤ)
