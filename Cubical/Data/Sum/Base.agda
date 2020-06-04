{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sum.Base where

open import Cubical.Core.Everything

private
  variable
    ℓ ℓ' : Level
    A B C D : Type ℓ

data _⊎_ (A : Type ℓ)(B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

rec : {C : Type ℓ} → (A → C) → (B → C) → A ⊎ B → C
rec f _ (inl x) = f x
rec _ g (inr y) = g y

elim : {C : A ⊎ B → Type ℓ} →  ((a : A) → C (inl a)) → ((b : B) → C (inr b))
       → (x : A ⊎ B) → C x
elim f _ (inl x) = f x
elim _ g (inr y) = g y

map : (A → C) → (B → D) → A ⊎ B → C ⊎ D
map f _ (inl x) = inl (f x)
map _ g (inr y) = inr (g y)
