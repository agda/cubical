{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sum.Base where

open import Cubical.Core.Everything

data _⊎_ {ℓ ℓ'} (P : Set ℓ) (Q : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  inl : P → P ⊎ Q
  inr : Q → P ⊎ Q

private
  variable
    ℓ : Level
    A B C D : Set ℓ

map-⊎ : (A → C) → (B → D) → A ⊎ B → C ⊎ D
map-⊎ f _ (inl x) = inl (f x)
map-⊎ _ g (inr y) = inr (g y)
