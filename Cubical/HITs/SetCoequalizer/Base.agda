{-

This file contains:

- Definition of set coequalizers as performed in https://1lab.dev/Data.Set.Coequaliser.html

-}
module Cubical.HITs.SetCoequalizer.Base where

open import Cubical.Core.Primitives

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

-- Set coequalizers as a higher inductive type
data SetCoequalizer {A : Type ℓ} {B : Type ℓ'} (f g : A → B) : Type (ℓ-max ℓ ℓ') where
  inc    : B → SetCoequalizer f g
  coeq   : (a : A) → inc (f a) ≡ inc (g a)
  squash : (x y : SetCoequalizer f g) → (p q : x ≡ y) → p ≡ q
