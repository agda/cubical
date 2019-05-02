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

- Export universe lifting

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Prelude where

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
    A : Type ℓ
    B : A → Type ℓ
    x y z : A

refl : x ≡ x
refl {x = x} = λ _ → x

sym : x ≡ y → y ≡ x
sym p i = p (~ i)

symP : {A : I → Type ℓ} → {x : A i0} → {y : A i1} →
       (p : PathP A x y) → PathP (λ i → A (~ i)) y x
symP p j = p (~ j)

cong : ∀ (f : (a : A) → B a) (p : x ≡ y) →
       PathP (λ i → B (p i)) (f x) (f y)
cong f p i = f (p i)

cong₂ : ∀ {C : (a : A) → (b : B a) → Type ℓ} →
        (f : (a : A) → (b : B a) → C a b) →
        (p : x ≡ y) →
        {u : B x} {v : B y} (q : PathP (λ i → B (p i)) u v) →
        PathP (λ i → C (p i) (q i)) (f x u) (f y v)
cong₂ f p q i = f (p i) (q i)

-- The filler of homogeneous path composition:
-- compPath-filler p q = PathP (λ i → x ≡ q i) p (p ∙ q)

compPath-filler : ∀ {x y z : A} → x ≡ y → y ≡ z → I → I → A
compPath-filler {x = x} p q j i =
  hfill (λ j → λ { (i = i0) → x
                  ; (i = i1) → q j }) (inS (p i)) j

_∙_ : x ≡ y → y ≡ z → x ≡ z
(p ∙ q) j = compPath-filler p q i1 j

-- The filler of heterogeneous path composition:
-- compPathP-filler p q = PathP (λ i → PathP (λ j → (compPath-filler (λ i → A i) B i j)) x (q i)) p (compPathP p q)

compPathP-filler : {A : I → Type ℓ} → {x : A i0} → {y : A i1} → {B_i1 : Type ℓ} {B : A i1 ≡ B_i1} → {z : B i1} →
  (p : PathP A x y) → (q : PathP (λ i → B i) y z) → ∀ (i j : I) → compPath-filler (λ i → A i) B j i
compPathP-filler {A = A} {x = x} {B = B} p q i =
  fill (λ j → compPath-filler (λ i → A i) B j i)
       (λ j → λ { (i = i0) → x ;
                   (i = i1) → q j }) (inS (p i))

compPathP : {A : I → Type ℓ} → {x : A i0} → {y : A i1} → {B_i1 : Type ℓ} {B : (A i1) ≡ B_i1} → {z : B i1} →
  (p : PathP A x y) → (q : PathP (λ i → B i) y z) → PathP (λ j → ((λ i → A i) ∙ B) j) x z
compPathP p q j = compPathP-filler p q j i1

_≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = x≡y ∙ y≡z


≡⟨⟩-syntax : (x : A) → x ≡ y → y ≡ z → x ≡ z
≡⟨⟩-syntax = _≡⟨_⟩_
infixr 2 ≡⟨⟩-syntax
syntax ≡⟨⟩-syntax x (λ i → B) y = x ≡[ i ]⟨ B ⟩ y

_∎ : (x : A) → x ≡ x
_ ∎ = refl

-- another definition of composition, useful for some proofs
compPath'-filler : ∀ {x y z : A} → x ≡ y → y ≡ z → I → I → A
compPath'-filler {z = z} p q j i =
  hfill (λ j → λ { (i = i0) → p (~ j)
                 ; (i = i1) → z }) (inS (q i)) j

_□_ : x ≡ y → y ≡ z → x ≡ z
(p □ q) j = compPath'-filler p q i1 j

□≡∙ : (p : x ≡ y) (q : y ≡ z) → p □ q ≡ p ∙ q
□≡∙ {x = x} {y = y} {z = z} p q i j = hcomp (λ k → \ { (i = i0) → compPath'-filler p q k j
                                             ; (i = i1) → compPath-filler p q k j
                                             ; (j = i0) → p ( ~ i ∧ ~ k)
                                             ; (j = i1) → q (k ∨ ~ i) }) (helper i j)
  where
    helper : PathP (λ i → p (~ i) ≡ q (~ i)) q p
    helper i j = hcomp (λ k → \ { (i = i0) → q (k ∧ j)
                                ; (i = i1) → p (~ k ∨ j)
                                ; (j = i0) → p (~ i ∨ ~ k)
                                ; (j = i1) → q (~ i ∧ k) })
                       y

-- Transport, subst and functional extensionality

-- transport is a special case of transp
transport : {A B : Type ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

-- Transporting in a constant family is the identity function (up to a
-- path). If we would have regularity this would be definitional.
transportRefl : (x : A) → transport refl x ≡ x
transportRefl {A = A} x i = transp (λ _ → A) i x

-- We want B to be explicit in subst
subst : (B : A → Type ℓ') (p : x ≡ y) → B x → B y
subst B p pa = transport (λ i → B (p i)) pa

substRefl : (px : B x) → subst B refl px ≡ px
substRefl px = transportRefl px

funExt : {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
funExt p i x = p x i

-- J for paths and its computation rule

module _ (P : ∀ y → x ≡ y → Type ℓ') (d : P x refl) where
  J : (p : x ≡ y) → P y p
  J p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

  JRefl : J refl ≡ d
  JRefl = transportRefl d

-- Contractibility of singletons

singl : (a : A) → Type _
singl {A = A} a = Σ[ x ∈ A ] (a ≡ x)

contrSingl : (p : x ≡ y) → Path (singl x) (x , refl) (y , p)
contrSingl p i = (p i , λ j → p (i ∧ j))


-- Converting to and from a PathP

module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where
  toPathP : transp A i0 x ≡ y → PathP A x y
  toPathP p i = hcomp (λ j → λ { (i = i0) → x
                               ; (i = i1) → p j })
                      (transp (λ j → A (i ∧ j)) (~ i) x)

  fromPathP : PathP A x y → transp A i0 x ≡ y
  fromPathP p i = transp (λ j → A (i ∨ j)) i (p i)


-- Direct definitions of lower h-levels

isContr : Type ℓ → Type ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)

isSet' : Type ℓ → Type ℓ
isSet' A = {x y z w : A} (p : x ≡ y) (q : z ≡ w) (r : x ≡ z) (s : y ≡ w) →
           PathP (λ i → Path A (r i) (s i)) p q

isGroupoid : Type ℓ → Type ℓ
isGroupoid A = ∀ a b → isSet (Path A a b)

is2Groupoid : Type ℓ → Type ℓ
is2Groupoid A = ∀ a b → isGroupoid (Path A a b)

-- Essential consequences of isProp and isContr
isProp→PathP
  : ((x : A) → isProp (B x)) → {a0 a1 : A}
  → (p : a0 ≡ a1) (b0 : B a0) (b1 : B a1)
  → PathP (λ i → B (p i)) b0 b1
isProp→PathP {B = B} P p b0 b1 = toPathP {A = λ i → B (p i)} {b0} {b1} (P _ _ _)

isPropIsContr : isProp (isContr A)
isPropIsContr z0 z1 j =
  ( z0 .snd (z1 .fst) j
  , λ x i → hcomp (λ k → λ { (i = i0) → z0 .snd (z1 .fst) j
                           ; (i = i1) → z0 .snd x (j ∨ k)
                           ; (j = i0) → z0 .snd x (i ∧ k)
                           ; (j = i1) → z1 .snd x i })
                  (z0 .snd (z1 .snd x i) j))

isContr→isProp : isContr A → isProp A
isContr→isProp (x , p) a b i =
  hcomp (λ j → λ { (i = i0) → p a j
                 ; (i = i1) → p b j }) x

isProp→isSet : isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp (λ k → λ { (i = i0) → h a a k
                 ; (i = i1) → h a b k
                 ; (j = i0) → h a (p i) k
                 ; (j = i1) → h a (q i) k }) a

-- Universe lifting

record Lift {i j} (A : Type i) : Type (ℓ-max i j) where
  instance constructor lift
  field
    lower : A

open Lift public
