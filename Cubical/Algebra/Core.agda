{-# OPTIONS --safe #-}
module Cubical.Algebra.Core where

open import Cubical.Foundations.Prelude

private variable
  ℓ : Level

Op₁ : Type ℓ → Type ℓ
Op₁ A = A → A

Op₂ : Type ℓ → Type ℓ
Op₂ A = A → A → A
