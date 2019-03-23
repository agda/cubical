{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sum.Base where

open import Cubical.Core.Everything

data _⊎_ {ℓ ℓ'} (P : Set ℓ) (Q : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  inl : P → P ⊎ Q
  inr : Q → P ⊎ Q

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A : Set ℓ
    B : Set ℓ'
    C : Set ℓ''
    D : Set ℓ'''

elim-⊎ : {C : A ⊎ B → Set ℓ''} →  ((a : A) → C (inl a)) → ((b : B) → C (inr b))
       → (x : A ⊎ B) → C x
elim-⊎ f g (inl x) = f x
elim-⊎ f g (inr y) = g y

map-⊎ : (A → C) → (B → D) → A ⊎ B → C ⊎ D
map-⊎ f _ (inl x) = inl (f x)
map-⊎ _ g (inr y) = inr (g y)
