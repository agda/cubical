{-# OPTIONS --safe #-}
module Cubical.Data.List.Base where

open import Agda.Builtin.List public
open import Cubical.Core.Everything
open import Cubical.Data.Maybe.Base as Maybe
open import Cubical.Data.Nat.Base

module _ {ℓ} {A : Type ℓ} where

  infixr 5 _++_
  infixl 5 _∷ʳ_

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

  map : ∀ {ℓ'} {B : Type ℓ'} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  map2 : ∀ {ℓ' ℓ''} {B : Type ℓ'} {C : Type ℓ''}
    → (A → B → C) → List A → List B → List C
  map2 f [] _ = []
  map2 f _ [] = []
  map2 f (x ∷ xs) (y ∷ ys) = f x y ∷ map2 f xs ys

  filterMap : ∀ {ℓ'} {B : Type ℓ'} → (A → Maybe B) → List A → List B
  filterMap f [] = []
  filterMap f (x ∷ xs) = Maybe.rec (filterMap f xs) (_∷ filterMap f xs) (f x)

  foldr : ∀ {ℓ'} {B : Type ℓ'} → (A → B → B) → B → List A → B
  foldr f b [] = b
  foldr f b (x ∷ xs) = f x (foldr f b xs)

  foldl : ∀ {ℓ'} {B : Type ℓ'} → (B → A → B) → B → List A → B
  foldl f b [] = b
  foldl f b (x ∷ xs) = foldl f (f b x) xs
