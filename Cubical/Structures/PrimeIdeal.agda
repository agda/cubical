{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.PrimeIdeal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic using (_⊔_; [_])
open import Cubical.Structures.Ring
open import Cubical.Structures.Ideal

private
  variable
    ℓ : Level

module _ (R : Ring {ℓ}) where
  open ring-·syntax R

  isPrimeIdeal : (P : Ideal R) → hProp _
  isPrimeIdeal (P , _) = ((x y : ⟨ R ⟩) → x · y ∈ P → [ P(x) ⊔ P(y) ])
                         , isPropΠ3 λ x y _ → snd (P(x) ⊔ P(y))

