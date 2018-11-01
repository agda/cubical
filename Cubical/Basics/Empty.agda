{-# OPTIONS --cubical #-}
module Cubical.Basics.Empty where

data ⊥ : Set where

⊥-elim : ∀ {l} {A : Set l} → ⊥ → A
⊥-elim ()

¬_ : ∀ {l} → Set l → Set l
¬ A = A → ⊥
