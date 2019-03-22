{-# OPTIONS --cubical --safe #-}
module Cubical.Data.DiffInt.Base where

open import Cubical.HITs.SetQuotients.Base
open import Cubical.Data.Nat

open import Cubical.Foundations.HLevels

open import Cubical.Core.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.Binary.Base

open import Cubical.Core.Glue
open import Cubical.Foundations.Equiv
open import Cubical.Data.Prod
open import Cubical.Data.Sigma

rel : (ℕ ×Σ ℕ) → (ℕ ×Σ ℕ) → Set
rel (a₀ , b₀) (a₁ , b₁) = x ≡ y
  where
    x = a₀ + b₁
    y = a₁ + b₀

ℤ = (ℕ ×Σ ℕ) / rel

