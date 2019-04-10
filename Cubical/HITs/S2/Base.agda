{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.S2.Base where

open import Cubical.Core.Primitives

open import Cubical.Foundations.Prelude

data S² : Set where
  base : S²
  surf : PathP (λ i → base ≡ base) refl refl
