{-# OPTIONS --cubical --safe #-}

module Cubical.Foundations.FunExtEquiv where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

-- Function extensionality is an equivalence.
module _ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} where
  private
    appl : f ≡ g → ∀ x → f x ≡ g x
    appl eq x i = eq i x

    fib : (p : f ≡ g) → fiber (funExt {B = B}) p
    fib p = (appl p , refl)

    funExt-fiber-isContr
      : (p : f ≡ g)
      → (fi : fiber (funExt {B = B}) p)
      → fib p ≡ fi
    funExt-fiber-isContr p (h , eq) i = (appl (eq (~ i)) , λ j → eq (~ i ∨ j))

  funExt-isEquiv : isEquiv (funExt {B = B})
  equiv-proof funExt-isEquiv p = (fib p , funExt-fiber-isContr p)

  funExtEquiv : (∀ x → f x ≡ g x) ≃ (f ≡ g)
  funExtEquiv = (funExt {B = B} , funExt-isEquiv)

  funExtPath : (∀ x → f x ≡ g x) ≡ (f ≡ g)
  funExtPath = ua funExtEquiv
