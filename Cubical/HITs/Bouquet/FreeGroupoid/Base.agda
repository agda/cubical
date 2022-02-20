{-

This file contains:

- An implementation of the free groupoid (a free group that has no limitiations
  over the high dimensional path structure). An intermediate construction used
  to calculate the fundamental group of a Bouquet.

-}
{-# OPTIONS --safe #-}

module Cubical.HITs.Bouquet.FreeGroupoid.Base where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level

data FreeGroupoid (A : Type ℓ) : Type ℓ where
  η     : A → FreeGroupoid A
  m     : FreeGroupoid A → FreeGroupoid A → FreeGroupoid A
  e     : FreeGroupoid A
  inv   : FreeGroupoid A → FreeGroupoid A
  assoc : ∀ x y z → m x (m y z) ≡ m (m x y) z
  idr   : ∀ x → x ≡ m x e
  idl   : ∀ x → x ≡  m e x
  invr  : ∀ x → m x (inv x) ≡ e
  invl  : ∀ x → m (inv x) x ≡ e
