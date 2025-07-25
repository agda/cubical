{-

This file contains:

- Definition of the Bouquet of circles of a type aka wedge of A circles

-}

module Cubical.HITs.Bouquet.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

private
  variable
    ℓ : Level

data Bouquet (A : Type ℓ) : Type ℓ where
  base : Bouquet A
  loop : A → base ≡ base

Bouquet∙ : Type ℓ → Pointed ℓ
Bouquet∙ A = Bouquet A , base
