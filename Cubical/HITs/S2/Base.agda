module Cubical.HITs.S2.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

data S² : Type₀ where
  base : S²
  surf : PathP (λ i → base ≡ base) refl refl

S²∙ : Pointed ℓ-zero
S²∙ = S² , base
