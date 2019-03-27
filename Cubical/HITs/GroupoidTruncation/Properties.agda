{-

This file contains:

- Properties of groupoid truncations

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.GroupoidTruncation.Properties where

open import Cubical.Core.Prelude
open import Cubical.HITs.GroupoidTruncation.Base

recGroupoidTrunc : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (gB : isGroupoid B) → (A → B) → (∥ A ∥₁ → B)
recGroupoidTrunc gB f ∣ x ∣₁ = f x
recGroupoidTrunc gB f (squash₁ _ _ _ _ r s i j k) =
  gB _ _ _ _
    (λ m n → recGroupoidTrunc gB f (r m n))
    (λ m n → recGroupoidTrunc gB f (s m n))
    i j k
