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

case_of_ : ∀{ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} → (x : A) → (∀ x → B x) → B x
case x of f = f x

case_return_of_ : ∀{ℓ ℓ'} {A : Set ℓ} (x : A) (B : A → Set ℓ') → (∀ x → B x) → B x
case x return P of f = f x
