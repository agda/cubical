{-
  Definitions for functions
-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Function where

open import Cubical.Core.Everything
open import Cubical.Core.Glue public using (idfun)

infixr 9 _∘_

_∘_ : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : A → Set ℓ′} {C : (a : A) → B a → Set ℓ″}
        (g : {a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)

∘-assoc : ∀ {ℓ ℓ′ ℓ″ ℓ‴} {A : Set ℓ} {B : A → Set ℓ′} {C : (a : A) → B a → Set ℓ″} {D : (a : A) (b : B a) → C a b → Set ℓ‴}
            (h : {a : A} {b : B a} → (c : C a b) → D a b c) (g : {a : A} → (b : B a) → C a b) (f : (a : A) → B a)
          → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
∘-assoc h g f i x = h (g (f x))

∘-idˡ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : A → Set ℓ′} (f : (a : A) → B a) → f ∘ idfun A ≡ f
∘-idˡ f i x = f x

∘-idʳ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : A → Set ℓ′} (f : (a : A) → B a) → (λ {a} → idfun (B a)) ∘ f ≡ f
∘-idʳ f i x = f x


const : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → A → B → A
const x = λ _ → x


case_of_ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} → (x : A) → (∀ x → B x) → B x
case x of f = f x

case_return_of_ : ∀ {ℓ ℓ'} {A : Set ℓ} (x : A) (B : A → Set ℓ') → (∀ x → B x) → B x
case x return P of f = f x
