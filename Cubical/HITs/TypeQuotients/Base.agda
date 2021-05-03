{-

This file contains:

- Definition of type quotients (i.e. non-truncated quotients)

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.TypeQuotients.Base where

open import Cubical.Core.Primitives

-- Type quotients as a higher inductive type:
data _/ₜ_ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  [_] : (a : A) → A /ₜ R
  eq/ : (a b : A) → (r : R a b) → [ a ] ≡ [ b ]

