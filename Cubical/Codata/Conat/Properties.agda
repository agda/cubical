{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Conat.Properties where

open import Cubical.Data.Unit

open import Cubical.Core.Everything

open import Cubical.Codata.Conat.Base

open Conat

succ : Conat → Conat
succ a = conat (psuc a)

Unwrap-prev : Pred Conat -> Set
Unwrap-prev  pzero   = Unit
Unwrap-prev (psuc _) = Conat

unwrap-prev : (n : Pred Conat) -> Unwrap-prev n
unwrap-prev  pzero   = _
unwrap-prev (psuc x) = x

private -- tests
  zero = conat pzero
  one  = succ zero
  two  = succ one

  succOne≡two : succ one ≡ two
  succOne≡two i = two

  predTwo≡one : unwrap-prev (prev two) ≡ one
  predTwo≡one i = one

∞ : Conat
prev ∞ = psuc ∞

∞+1≡∞ : succ ∞ ≡ ∞
prev (∞+1≡∞ _) = psuc ∞

∞+2≡∞ : succ (succ ∞) ≡ ∞
∞+2≡∞ = compPath (cong succ ∞+1≡∞) ∞+1≡∞

-- TODO: plus for conat, ∞ + ∞ ≡ ∞

