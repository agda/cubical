{-# OPTIONS --safe #-}
module Cubical.HITs.James.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

private
  variable
    ℓ : Level

module _
  ((X , x₀) : Pointed ℓ) where

  data James : Type ℓ where
    [] : James
    _∷_ : X → James → James
    unit : (xs : James) → xs ≡ x₀ ∷ xs

  infixr 5 _∷_
  infixr 5 _++_
  infixl 5 _∷ʳ_

  [_] : X → James
  [ x ] = x ∷ []

  _++_ : James → James → James
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ xs ++ ys
  (unit xs i) ++ ys = unit (xs ++ ys) i

  _∷ʳ_ : James → X → James
  xs ∷ʳ x = xs ++ x ∷ []
