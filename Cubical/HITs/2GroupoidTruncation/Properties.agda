{-

This file contains:

- Properties of 2-groupoid truncations

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.2GroupoidTruncation.Properties where

open import Cubical.Core.Prelude
open import Cubical.HITs.2GroupoidTruncation.Base

rec2GroupoidTrunc : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (gB : is2Groupoid B) → (A → B) → (∥ A ∥₂ → B)
rec2GroupoidTrunc gB f ∣ x ∣₂ = f x
rec2GroupoidTrunc gB f (squash₂ _ _ _ _ _ _ t u i j k l) =
  gB _ _ _ _ _ _
    (λ m n o → rec2GroupoidTrunc gB f (t m n o))
    (λ m n o → rec2GroupoidTrunc gB f (u m n o))
    i j k l
