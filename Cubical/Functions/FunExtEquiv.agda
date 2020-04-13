{-# OPTIONS --cubical --safe #-}
module Cubical.Functions.FunExtEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level

-- Function extensionality is an equivalence
module _ {A : Type ℓ} {B : A → Type ℓ₁} {f g : (x : A) → B x} where
  private
    fib : (p : f ≡ g) → fiber funExt p
    fib p = (funExt⁻ p , refl)

    funExt-fiber-isContr : (p : f ≡ g) → (fi : fiber funExt p) → fib p ≡ fi
    funExt-fiber-isContr p (h , eq) i = (funExt⁻ (eq (~ i)) , λ j → eq (~ i ∨ j))

  funExt-isEquiv : isEquiv funExt
  equiv-proof funExt-isEquiv p = (fib p , funExt-fiber-isContr p)

  funExtEquiv : (∀ x → f x ≡ g x) ≃ (f ≡ g)
  funExtEquiv = (funExt {B = B} , funExt-isEquiv)

  funExtPath : (∀ x → f x ≡ g x) ≡ (f ≡ g)
  funExtPath = ua funExtEquiv


-- Function extensionality for binary functions
funExt₂ : {A : Type ℓ} {B : A → Type ℓ₁} {C : (x : A) → B x → Type ℓ₂}
            {f g : (x : A) → (y : B x) → C x y}
          → ((x : A) (y : B x) → f x y ≡ g x y) → f ≡ g
funExt₂ p i x y = p x y i

-- Function extensionality for binary functions is an equivalence
module _ {A : Type ℓ} {B : A → Type ℓ₁} {C : (x : A) → B x → Type ℓ₂}
         {f g : (x : A) → (y : B x) → C x y} where
  private
    appl₂ : f ≡ g → ∀ x y → f x y ≡ g x y
    appl₂ eq x y i = eq i x y

    fib : (p : f ≡ g) → fiber funExt₂ p
    fib p = (appl₂ p , refl)

    funExt₂-fiber-isContr : (p : f ≡ g) → (fi : fiber funExt₂ p) → fib p ≡ fi
    funExt₂-fiber-isContr p (h , eq) i = (appl₂ (eq (~ i)) , λ j → eq (~ i ∨ j))

  funExt₂-isEquiv : isEquiv funExt₂
  equiv-proof funExt₂-isEquiv p = (fib p , funExt₂-fiber-isContr p)

  funExt₂Equiv : (∀ x y → f x y ≡ g x y) ≃ (f ≡ g)
  funExt₂Equiv = (funExt₂ , funExt₂-isEquiv)

  funExt₂Path : (∀ x y → f x y ≡ g x y) ≡ (f ≡ g)
  funExt₂Path = ua funExt₂Equiv


-- Function extensionality for ternary functions
funExt₃ : {A : Type ℓ} {B : A → Type ℓ₁} {C : (x : A) → B x → Type ℓ₂}
          {D : (x : A) → (y : B x) → C x y → Type ℓ₃}
          {f g : (x : A) → (y : B x) → (z : C x y) → D x y z}
        → ((x : A) (y : B x) (z : C x y) → f x y z ≡ g x y z) → f ≡ g
funExt₃ p i x y z = p x y z i

-- Function extensionality for ternary functions is an equivalence
module _ {A : Type ℓ} {B : A → Type ℓ₁} {C : (x : A) → B x → Type ℓ₂}
         {D : (x : A) → (y : B x) → C x y → Type ℓ₃}
         {f g : (x : A) → (y : B x) → (z : C x y) → D x y z} where
  private
    appl₃ : f ≡ g → ∀ x y z → f x y z ≡ g x y z
    appl₃ eq x y z i = eq i x y z

    fib : (p : f ≡ g) → fiber funExt₃ p
    fib p = (appl₃ p , refl)

    funExt₃-fiber-isContr : (p : f ≡ g) → (fi : fiber funExt₃ p) → fib p ≡ fi
    funExt₃-fiber-isContr p (h , eq) i = (appl₃ (eq (~ i)) , λ j → eq (~ i ∨ j))

  funExt₃-isEquiv : isEquiv funExt₃
  equiv-proof funExt₃-isEquiv p = (fib p , funExt₃-fiber-isContr p)

  funExt₃Equiv : (∀ x y z → f x y z ≡ g x y z) ≃ (f ≡ g)
  funExt₃Equiv = (funExt₃ , funExt₃-isEquiv)

  funExt₃Path : (∀ x y z → f x y z ≡ g x y z) ≡ (f ≡ g)
  funExt₃Path = ua funExt₃Equiv


-- Puzzle: Can one generalize this to n-ary functions?
