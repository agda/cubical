{-

This file contains:

- Definition of set quotients

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SetQuotients.Base where

open import Cubical.Core.Primitives

-- Set quotients as a higher inductive type:
data _/_ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  [_] : (a : A) → A / R
  eq/ : (a b : A) → (r : R a b) → [ a ] ≡ [ b ]
  squash/ : (x y : A / R) → (p q : x ≡ y) → p ≡ q
