{-

This file proves a variety of basic results about paths:

- refl, sym, cong and composition of paths. This is used to set up
  equational reasoning.

- Subst and functional extensionality

- J and its computation rule (up to a path)

- Σ-types and contractibility of singletons

- Converting PathP to and from a homogeneous path with transp


It should *not* depend on the Agda standard library.

-}
{-# OPTIONS --cubical #-}
module Cubical.Prelude where

open import Agda.Builtin.Sigma

open import Cubical.Core public

-- Basic theory about paths. These proofs should typically be
-- inlined. This module also makes equational reasoning work nicely
-- with (non-dependent) paths.
module _ {ℓ} {A : Set ℓ} where
  refl : {x : A} → x ≡ x
  refl {x = x} = λ _ → x

  sym : {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  cong : ∀ {ℓ'} {B : A → Set ℓ'} {x y : A}
         (f : (a : A) → B a) (p : x ≡ y)
       → PathP (λ i → B (p i)) (f x) (f y)
  cong f p = λ i → f (p i)

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


-- Subst and functional extensionality

module _ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} where
  subst : {a b : A} (p : a ≡ b) → B a → B b
  subst p pa = transp (λ i → B (p i)) i0 pa

  substRefl : {a : A} (pa : B a) → subst refl pa ≡ pa
  substRefl {a = a} pa i = transp (λ _ → B a) i pa

  funExt : {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
  funExt p = λ i x → p x i


-- Transporting in a constant family is the identity function (up to a
-- path). If we would have regularity this would be definitional.
transpRefl : ∀ {ℓ} (A : Set ℓ) (u0 : A) →
             PathP (λ _ → A) (transp (λ _ → A) i0 u0) u0
transpRefl A u0 i = transp (λ _ → A) i u0


-- J for paths and its computation rule

module _ {ℓ ℓ'} {A : Set ℓ} {x : A}
         (P : ∀ y → x ≡ y → Set ℓ') (d : P x refl) where
  J : {y : A} → (p : x ≡ y) → P y p
  J p = transp (λ i → P (p i) (λ j → p (i ∧ j))) i0 d

  JRefl : J refl ≡ d
  JRefl i = transp (λ _ → P x refl) i d


-- Σ-types

_×_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
A × B = Σ A (λ _ → B)

infixr 2 _×_
infix 2 Σ-syntax

Σ-syntax : ∀ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ-max ℓ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B


-- Contractibility of singletons

module _ {ℓ} {A : Set ℓ} where
  singl : (a : A) → Set ℓ
  singl a = Σ[ x ∈ A ] (a ≡ x)

  contrSingl : {a b : A} (p : a ≡ b) → Path (singl a) (a , refl) (b , p)
  contrSingl p i = (p i , λ j → p (i ∧ j))


-- Converting to and from a PathP

module _ {ℓ} {A : I → Set ℓ} {x : A i0} {y : A i1} where
  toPathP : transp A i0 x ≡ y → PathP A x y
  toPathP p i = hcomp (A i) _
                      (λ j → λ { (i = i0) → x ; (i = i1) → p j })
                      (transp (λ j → A (i ∧ j)) (~ i) x)

  fromPathP : PathP A x y → transp A i0 x ≡ y
  fromPathP p i = transp (λ j → A (i ∨ j)) i (p i)

