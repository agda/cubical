{-# OPTIONS --cubical --safe #-}
module Cubical.Data.DiffInt.Base where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.SetQuotients.Base

open import Cubical.Data.Prod
open import Cubical.Data.Nat

rel : (ℕ ×Σ ℕ) → (ℕ ×Σ ℕ) → Type₀
rel (a₀ , b₀) (a₁ , b₁) = x ≡ y
  where
    x = a₀ + b₁
    y = a₁ + b₀

ℤ = (ℕ ×Σ ℕ) / rel

