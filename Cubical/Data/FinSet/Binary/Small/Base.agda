{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.Binary.Small.Base where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence


open import Cubical.Data.Bool hiding (isSetBool)

data Binary : Type₀
El : Binary → Type₀

data Binary where
  ℕ₂ : Binary
  un : ∀ x y → El x ≃ El y → x ≡ y

El ℕ₂ = Bool
El (un _ _ e i) = ua e i
