{-# OPTIONS --cubical --safe #-}
module Cubical.Data.List.Base where

open import Agda.Builtin.List
open import Cubical.Core.Everything

module _ {ℓ} {A : Type ℓ} where

  infixr 5 _++_

  [_] : A → List A
  [ a ] = a ∷ []

  _++_ : List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ xs ++ ys

  rev : List A → List A
  rev [] = []
  rev (x ∷ xs) = rev xs ++ [ x ]

