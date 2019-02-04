{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Conat.Properties where

open import Agda.Builtin.Unit

open import Cubical.Core.Everything

open import Cubical.Codata.Conat.Base

open Conat

succ : Conat → Conat
succ a = conat (psuc a)

Unwrap-pred : Pred Conat -> Set
Unwrap-pred  pzero   = ⊤
Unwrap-pred (psuc _) = Conat

unwrap-pred : (n : Pred Conat) -> Unwrap-pred n
unwrap-pred  pzero   = _
unwrap-pred (psuc x) = x

private -- tests
  zero = conat pzero
  one  = succ zero
  two  = succ one

  succOne≡two : succ one ≡ two
  succOne≡two i = two

  predTwo≡one : unwrap-pred (pred two) ≡ one
  predTwo≡one i = one

∞ : Conat
pred ∞ = psuc ∞

∞+1≡∞ : succ ∞ ≡ ∞
pred (∞+1≡∞ _) = psuc ∞

∞+2≡∞ : succ (succ ∞) ≡ ∞
∞+2≡∞ = compPath (cong succ ∞+1≡∞) ∞+1≡∞

-- TODO: plus for conat, ∞ + ∞ ≡ ∞

