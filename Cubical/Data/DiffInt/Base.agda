{-# OPTIONS --cubical --safe #-}
module Cubical.Data.DiffInt.Base where

open import Cubical.HITs.SetQuotients
open import Cubical.Data.Nat

open import Cubical.Foundations.HLevels

open import Cubical.Core.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (ℓ-max a b)
A × B = Σ[ x ∈ A ] B

rel : (ℕ × ℕ) → (ℕ × ℕ) → Σ Set isProp
rel (a₀ , b₀) (a₁ , b₁) =
  (x ≡ y), (isSetℕ x y)
  where
    x = a₀ + b₁
    y = b₀ + a₁

ℤ = (ℕ × ℕ) / rel

discreteℤ : Discrete ℤ
discreteℤ = elimSetQuotients {B = λ z₀ → ∀ z₁ → Dec (z₀ ≡ z₁)} (λ z₀ → {!hLevelPi 1 (λ z₁ → ?)!}) {!!} {!!}
