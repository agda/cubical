{- 

This file proves a variety of basic results about paths.

It should *not* depend on the Agda standard library.

 -}
{-# OPTIONS --cubical #-}
module Cubical.Prelude where

open import Cubical.Core public


-- Transporting in a constant family is the identity function (up to a
-- path). If we would have regularity this would be definitional.
lemTranspConst : ∀ {ℓ} (A : Set ℓ) (u0 : A) →
                 PathP (λ _ → A) (transp (λ _ → A) i0 u0) u0
lemTranspConst A u0 i = transp (λ _ → A) i u0


-- Basic theory about paths. These proofs should typically be
-- inlined. This module also makes equational reasoning work nicely
-- with (non-dependent) paths.
module _ {ℓ} {A : Set ℓ} where
  refl : {x : A} → x ≡ x
  refl {x = x} = λ _ → x

  sym : {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  cong-d : ∀ {ℓ'} {B : A → Set ℓ'} {x y : A}
    → (f : (a : A) → B a) → (p : x ≡ y)
    → PathP (λ i → B (p i)) (f x) (f y)
  cong-d f p = λ i → f (p i)

  cong : ∀ {ℓ'} {B : Set ℓ'} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong = cong-d

  -- This is called compPath and not trans in order to eliminate
  -- confusion with transp
  compPath : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  compPath {x = x} p q i =
    hcomp A _ (λ j → \ { (i = i0) → x
                       ; (i = i1) → q j }) (p i)

  infix  3 _≡-qed _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  1 ≡-proof_ begin_

  ≡-proof_ begin_ : {x y : A} → x ≡ y → x ≡ y
  ≡-proof x≡y = x≡y
  begin_ = ≡-proof_

  _≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = compPath x≡y y≡z

  _≡-qed _∎ : (x : A) → x ≡ x
  _ ≡-qed  = refl
  _∎ = _≡-qed




