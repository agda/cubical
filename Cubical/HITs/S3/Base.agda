{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.S3.Base where

open import Cubical.Foundations.Prelude

data S³ : Type₀ where
  base : S³
  surf : PathP (λ j → PathP (λ i → base ≡ base) refl refl) refl refl

