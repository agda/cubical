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
sym p = λ i → p (~ i)

cong : ∀ {B : A → Set ℓ'} (f : (a : A) → B a) (p : x ≡ y)
       → PathP (λ i → B (p i)) (f x) (f y)
cong f p = λ i → f (p i)

compPath-sides : ∀{ℓ} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → (i j : I) → Partial (~ i ∨ i) A
compPath-sides {x = x} p q i j = \ { (i = i0) → x
                                   ; (i = i1) → q j }

compPath-bot : ∀{ℓ} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → (i : I) → A
compPath-bot p q i = p i

-- This is called compPath and not trans in order to eliminate
-- confusion with transp
compPath : x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i =
  hcomp (compPath-sides p q i) (compPath-bot p q i)

compPath'-sides : ∀{ℓ} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → (i j : I) → Partial (~ i ∨ i) A
compPath'-sides {z = z} p q i j = \ { (i = i0) → p (~ j)
                                   ; (i = i1) → z }

compPath'-bot : ∀{ℓ} {A : Set ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → (i : I) → A
compPath'-bot p q i = q i

compPath' : ∀ {x y z : A} → x ≡ y → y ≡ z → x ≡ z
compPath' {z = z} p q i = hcomp (compPath'-sides p q i) (compPath'-bot p q i)

compPath≡compPath' : ∀ {x y z : A} (p : x ≡ y) (q : y ≡ z) → compPath p q ≡ compPath' p q
compPath≡compPath' {A = A} {x = x} {y = y} {z = z} p q i j = hcomp (λ k → \ { (i = i0) → hfill (compPath-sides p q j) (inc (compPath-bot p q j)) k
                                             ; (i = i1) → hfill (compPath'-sides p q j) (inc (compPath'-bot p q j)) k
                                             ; (j = i0) → p (i ∧ (~ k))
                                             ; (j = i1) → q (i ∨ k) }) (helper i j)
  where
    helper : PathP (λ i → p i ≡ q i) p q
    helper i j = hcomp (λ k → \ { (i = i0) → p (~ k ∨ j)
                                ; (i = i1) → q (k ∧ j)
                                ; (j = i0) → p (i ∨ (~ k))
                                ; (j = i1) → q (i ∧ k) })
                       y


rInv : (p : x ≡ y) → compPath p (sym p) ≡ refl
rInv {x = x} p i j = hcomp (λ k → \ { (i = i0) → hfill (compPath-sides p (sym p) j)
                                                 (inc (compPath-bot p (sym p) j)) k
                              ; (i = i1) → p (j ∧ (~ k))
                              ; (j = i0) → x
                              ; (j = i1) → p (~ k) })
                     (p j)

rUnit : (p : x ≡ y) → compPath p refl ≡ p
rUnit {x = x} {y = y} p i j =
  hcomp (λ k → \ { (i = i0) → hfill (compPath-sides p refl j)
                               (inc (compPath-bot p refl j)) k
                 ; (i = i1) → p j
                 ; (j = i0) → x
                 ; (j = i1) → y }) (p j)

compPath-assoc' : {w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → compPath (compPath p q) r ≡ compPath p (compPath' q r)
compPath-assoc' {x = x} p q r i j = hcomp (λ k → \ { (i = i0) → hfill (compPath-sides (compPath p q) r j)
                                                                      (inc (compPath-bot (compPath p q) r j)) k
                                                   ; (i = i1) → hfill (compPath-sides p (compPath' q r) j)
                                                                      (inc (compPath-bot p (compPath' q r) j)) k
                                                   ; (j = i0) → x
                                                   ; (j = i1) → hfill (compPath'-sides q r k)
                                                                       (inc (compPath'-bot q r k)) i })
                                          (hfill (compPath-sides p q j)
                                                 (inc (compPath-bot p q j)) (~ i))

compPath-assoc : {w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → compPath (compPath p q) r ≡ compPath p (compPath q r)
compPath-assoc p q r = compPath (compPath-assoc' p q r) (cong (compPath p) (sym (compPath≡compPath' q r)))

infix  3 _∎
infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = compPath x≡y y≡z

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

infixl 30 _×_
_×_ : (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
A × B = Σ[ x ∈ A ] B

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

isSet' : Set ℓ → Set ℓ
isSet' A = {x y z w : A} (p : x ≡ y) (q : z ≡ w) (r : x ≡ z) (s : y ≡ w) →
           PathP (λ i → Path A (r i) (s i)) p q
