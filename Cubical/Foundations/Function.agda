{-
  Definitions for functions
-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Function where

open import Cubical.Core.Everything

-- The identity function
idfun : ∀ {ℓ} → (A : Type ℓ) → A → A
idfun _ x = x

infixr 9 _∘_

_∘_ : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ} {B : A → Type ℓ′} {C : (a : A) → B a → Type ℓ″}
        (g : {a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)

∘-assoc : ∀ {ℓ ℓ′ ℓ″ ℓ‴} {A : Type ℓ} {B : A → Type ℓ′} {C : (a : A) → B a → Type ℓ″} {D : (a : A) (b : B a) → C a b → Type ℓ‴}
            (h : {a : A} {b : B a} → (c : C a b) → D a b c) (g : {a : A} → (b : B a) → C a b) (f : (a : A) → B a)
          → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
∘-assoc h g f i x = h (g (f x))

∘-idˡ : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} (f : (a : A) → B a) → f ∘ idfun A ≡ f
∘-idˡ f i x = f x

∘-idʳ : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} (f : (a : A) → B a) → (λ {a} → idfun (B a)) ∘ f ≡ f
∘-idʳ f i x = f x


const : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → A → B → A
const x = λ _ → x


case_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → (x : A) → (∀ x → B x) → B x
case x of f = f x

case_return_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} (x : A) (B : A → Type ℓ') → (∀ x → B x) → B x
case x return P of f = f x

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  -- Notions of 'coherently constant' functions for low dimensions.
  -- These are the properties of functions necessary to e.g. eliminate
  -- from the propositional truncation.

  -- 2-Constant functions are coherently constant if B is a set.
  2-Constant : (A → B) → Type _
  2-Constant f = ∀ x y → f x ≡ f y

  -- 3-Constant functions are coherently constant if B is a groupoid.
  3-Constant : (A → B) → Type _
  3-Constant f
    = Σ[ kf ∈ 2-Constant f ] ∀ x y z
    → PathP (λ i → f x ≡ kf y z i) (kf x y) (kf x z)
