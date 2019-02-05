{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Conat.Properties where

open import Cubical.Data.Unit
open import Cubical.Data.Sum

open import Cubical.Core.Everything

open import Cubical.Codata.Conat.Base

Unwrap-prev : Prev -> Set
Unwrap-prev  zero   = Unit
Unwrap-prev (suc _) = Conat

unwrap-prev : (n : Prev) -> Unwrap-prev n
unwrap-prev  zero   = _
unwrap-prev (suc x) = x

private -- tests
  𝟘 = conat zero
  one  = succ 𝟘
  two  = succ one

  succOne≡two : succ one ≡ two
  succOne≡two i = two

  predTwo≡one : unwrap-prev (prev two) ≡ one
  predTwo≡one i = one

∞ : Conat
prev ∞ = suc ∞

∞+1≡∞ : succ ∞ ≡ ∞
prev (∞+1≡∞ _) = suc ∞

∞+2≡∞ : succ (succ ∞) ≡ ∞
∞+2≡∞ = compPath (cong succ ∞+1≡∞) ∞+1≡∞

-- TODO: plus for conat, ∞ + ∞ ≡ ∞

