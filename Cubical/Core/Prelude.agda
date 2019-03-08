{-

This file proves a variety of basic results about paths:

- refl, sym, cong and composition of paths. This is used to set up
  equational reasoning.

- Transport, subst and functional extensionality

- J and its computation rule (up to a path)

- Σ-types and contractibility of singletons

- Converting PathP to and from a homogeneous path with transp

- Direct definitions of lower h-levels

- Export natural numbers

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Core.Prelude where

open import Agda.Builtin.Sigma public

open import Cubical.Core.Primitives public

infixr 30 _∙_
infix  3 _∎
infixr 2 _≡⟨_⟩_

-- Basic theory about paths. These proofs should typically be
-- inlined. This module also makes equational reasoning work with
-- (non-dependent) paths.

private
  variable
    ℓ ℓ' : Level
    A : Set ℓ
    x y z : A

refl : x ≡ x
refl {x = x} = λ _ → x

sym : x ≡ y → y ≡ x
sym p i = p (~ i)

symP : {A : I → Set ℓ} → {x : A i0} → {y : A i1} →
       (p : PathP A x y) → PathP (λ i → A (~ i)) y x
symP p j = p (~ j) 

cong : ∀ {B : A → Set ℓ'} (f : (a : A) → B a) (p : x ≡ y) →
       PathP (λ i → B (p i)) (f x) (f y)
cong f p = λ i → f (p i)

-- The filler of homogeneous path composition:
-- compPath-filler p q = PathP (λ i → x ≡ q i) p (p ∙ q)

compPath-filler : ∀ {x y z : A} → x ≡ y → y ≡ z → I → I → A
compPath-filler {x = x} p q j i =
  hfill (λ j → λ { (i = i0) → x
                  ; (i = i1) → q j }) (inc (p i)) j

_∙_ :  {x y z : A} → x ≡ y → y ≡ z → x ≡ z
(p ∙ q) j = compPath-filler p q i1 j

-- The filler of heterogeneous path composition:
-- compPathP-filler p q = PathP (λ i → PathP (λ j → (compPath-filler (λ i → A i) B i j)) x (q i)) p (compPathP p q)

compPathP-filler : {A : I → Set ℓ} → {x : A i0} → {y : A i1} → {B_i1 : Set ℓ} {B : A i1 ≡ B_i1} → {z : B i1} →
  (p : PathP A x y) → (q : PathP (λ i → B i) y z) → ∀ (i j : I) → compPath-filler (λ i → A i) B j i
compPathP-filler {A = A} {x = x} {B = B} p q i =
  fill (λ j → compPath-filler (λ i → A i) B j i)
       (λ j → λ { (i = i0) → x ;
                   (i = i1) → q j }) (inc (p i))

compPathP : {A : I → Set ℓ} → {x : A i0} → {y : A i1} → {B_i1 : Set ℓ} {B : (A i1) ≡ B_i1} → {z : B i1} →
  (p : PathP A x y) → (q : PathP (λ i → B i) y z) → PathP (λ j → ((λ i → A i) ∙ B) j) x z
compPathP p q j = compPathP-filler p q j i1

_≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = x≡y ∙ y≡z

_∎ : (x : A) → x ≡ x
_ ∎ = refl

-- Transport, subst and functional extensionality

-- transport is a special case of transp
transport : {A B : Set ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

-- Transporting in a constant family is the identity function (up to a
-- path). If we would have regularity this would be definitional.
transportRefl : (x : A) → transport refl x ≡ x
transportRefl {A = A} x i = transp (λ _ → A) i x

-- We want B to be explicit in subst
subst : (B : A → Set ℓ') (p : x ≡ y) → B x → B y
subst B p pa = transport (λ i → B (p i)) pa

substRefl : {B : A → Set ℓ'} (px : B x) → subst B refl px ≡ px
substRefl px = transportRefl px

funExt : {B : A → Set ℓ'} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
funExt p i x = p x i

-- J for paths and its computation rule

module _ (P : ∀ y → x ≡ y → Set ℓ') (d : P x refl) where
  J : (p : x ≡ y) → P y p
  J p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

  JRefl : J refl ≡ d
  JRefl = transportRefl d

-- Σ-types
infix 2 Σ-syntax

Σ-syntax : (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ-max ℓ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B


-- Contractibility of singletons

singl : {A : Set ℓ} (a : A) → Set ℓ
singl {A = A} a = Σ[ x ∈ A ] (a ≡ x)

contrSingl : (p : x ≡ y) → Path (singl x) (x , refl) (y , p)
contrSingl p i = (p i , λ j → p (i ∧ j))


-- Converting to and from a PathP

module _ {A : I → Set ℓ} {x : A i0} {y : A i1} where
  toPathP : transp A i0 x ≡ y → PathP A x y
  toPathP p i = hcomp (λ j → λ { (i = i0) → x
                               ; (i = i1) → p j })
                      (transp (λ j → A (i ∧ j)) (~ i) x)

  fromPathP : PathP A x y → transp A i0 x ≡ y
  fromPathP p i = transp (λ j → A (i ∨ j)) i (p i)


-- Direct definitions of lower h-levels

isContr : Set ℓ → Set ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

isProp : Set ℓ → Set ℓ
isProp A = (x y : A) → x ≡ y

isSet : Set ℓ → Set ℓ
isSet A = (x y : A) → isProp (x ≡ y)
