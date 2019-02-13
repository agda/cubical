{-
  Definitions for functions
-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Function where

open import Cubical.Core.Everything

infixr 9 _∘_

_∘_ : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : A → Set ℓ′} {C : (a : A) → B a → Set ℓ″}
        (g : {a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)
