{-

This file contains:

- An implementation of the free group of a type of generators as a HIT

-}
{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.Base where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level

data FreeGroup (A : Type ℓ) : Type ℓ where
  η     : A → FreeGroup A
  m     : FreeGroup A → FreeGroup A → FreeGroup A
  e     : FreeGroup A
  inv   : FreeGroup A → FreeGroup A
  assoc : ∀ x y z → m x (m y z) ≡ m (m x y) z
  idr   : ∀ x → x ≡ m x e
  idl   : ∀ x → x ≡  m e x
  invr  : ∀ x → m x (inv x) ≡ e
  invl  : ∀ x → m (inv x) x ≡ e
  trunc : ∀ x y → ∀ (p q : x ≡ y) → p ≡ q
