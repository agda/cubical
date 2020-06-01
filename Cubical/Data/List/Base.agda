{-# OPTIONS --cubical --safe #-}
module Cubical.Data.List.Base where

open import Agda.Builtin.List        public
open import Cubical.Core.Everything
open import Cubical.Data.Nat

module _ {ℓ} {A : Type ℓ} where

  infixr 5 _++_ _∷ʳ_

  [_] : A → List A
  [ a ] = a ∷ []

  _++_ : List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ xs ++ ys

  rev : List A → List A
  rev [] = []
  rev (x ∷ xs) = rev xs ++ [ x ]

  _∷ʳ_ : List A → A → List A
  xs ∷ʳ x = xs ++ x ∷ []

  length : List A → ℕ
  length [] = 0
  length (x ∷ l) = 1 + length l

  foldr : ∀ {ℓ'} {B : Type ℓ'} → (A → B → B) → B → List A → B
  foldr f b [] = b
  foldr f b (x ∷ xs) = f x (foldr f b xs)
