{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.S3.Base where

open import Cubical.Core.Primitives

open import Cubical.Foundations.Prelude

data S³ : Set where
  base : S³
  surf : PathP (λ j → PathP (λ i → base ≡ base) refl refl) refl refl

