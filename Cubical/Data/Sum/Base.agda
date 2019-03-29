{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sum.Base where

open import Cubical.Core.Everything

private
  variable
    ℓ ℓ' : Level
    A B C D : Set ℓ

data _⊎_ (A : Set ℓ)(B : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

elim-⊎ : {C : A ⊎ B → Set ℓ} →  ((a : A) → C (inl a)) → ((b : B) → C (inr b))
       → (x : A ⊎ B) → C x
elim-⊎ f _ (inl x) = f x
elim-⊎ _ g (inr y) = g y

map-⊎ : (A → C) → (B → D) → A ⊎ B → C ⊎ D
map-⊎ f _ (inl x) = inl (f x)
map-⊎ _ g (inr y) = inr (g y)

