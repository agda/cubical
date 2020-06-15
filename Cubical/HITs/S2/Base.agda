{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.S2.Base where

open import Cubical.Foundations.Prelude

data S² : Type₀ where
  base : S²
  surf : PathP (λ i → base ≡ base) refl refl
