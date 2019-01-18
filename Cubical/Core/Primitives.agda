{-

This file document and export the main primitives of Cubical Agda. It
also defines some basic derived operations (composition and filling).

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Core.Primitives where

open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.Sub public

open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; isOneEmpty     to empty
           ; primComp       to compCCHM  -- This should not be used
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )
open import Agda.Primitive public
  using    ( Level )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max )

-- This file document the Cubical Agda primitives. The primitives
-- themselves are bound by the Agda files imported above.

-- * The Interval
-- I : Setω

-- Endpoints, Connections, Reversal
-- i0 i1   : I
-- _∧_ _∨_ : I → I → I
-- ~_      : I → I


-- * Dependent path type. (Path over Path)

-- Introduced with lambda abstraction and eliminated with application,
-- just like function types.

-- PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

infix 4 _[_≡_]

_[_≡_] : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
_[_≡_] = PathP


-- Non dependent path types

Path : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
Path A a b = PathP (λ _ → A) a b

-- PathP (λ i → A) x y gets printed as x ≡ y when A does not mention i.
--  _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
--  _≡_ {A = A} = PathP (λ _ → A)


-- * @IsOne r@ represents the constraint "r = i1".
-- Often we will use "φ" for elements of I, when we intend to use them
-- with IsOne (or Partial[P]).
-- IsOne : I → Set

-- i1 is indeed equal to i1.
-- 1=1 : IsOne i1


-- * Types of partial elements, and their dependent version.

-- "Partial φ A" is a special version of "IsOne φ → A" with a more
-- extensional judgmental equality.
-- "PartialP φ A" allows "A" to be defined only on "φ".

-- Partial : ∀ {ℓ} → Set ℓ → I → Setω
-- PartialP : ∀ {ℓ} → (φ : I) → Partial (Set ℓ) φ → Setω

-- Partial elements are introduced by pattern matching with (r = i0)
-- or (r = i1) constraints, like so:

private
  sys : ∀ i → Partial (i ∨ ~ i) Set₁
  sys i (i = i0) = Set
  sys i (i = i1) = Set → Set

  -- It also works with pattern matching lambdas:
  --  http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.PatternMatchingLambdas
  sys' : ∀ i → Partial (i ∨ ~ i) Set₁
  sys' i = λ { (i = i0) → Set
             ; (i = i1) → Set → Set
             }

  -- When the cases overlap they must agree.
  sys2 : ∀ i j → Partial (i ∨ (i ∧ j)) Set₁
  sys2 i j = λ { (i = i1)          → Set
               ; (i = i1) (j = i1) → Set
               }

  -- (i0 = i1) is actually absurd.
  sys3 : Partial i0 Set₁
  sys3 = λ { () }


-- * There are cubical subtypes as in CCHM. Note that these are not
-- fibrant (hence in Setω):

_[_↦_] : ∀ {ℓ} (A : Set ℓ) (φ : I) (u : Partial φ A) → Agda.Primitive.Setω
A [ φ ↦ u ] = Sub A φ u

infix 4 _[_↦_]

-- Any element u : A can be seen as an element of A [ φ ↦ u ] which
-- agrees with u on φ:

-- inc : ∀ {ℓ} {A : Set ℓ} {φ} (u : A) → A [ φ ↦ (λ _ → u) ]

-- One can also forget that an element agrees with u on φ:

ouc : ∀ {ℓ} {A : Set ℓ} {φ : I} {u : Partial φ A} → A [ φ ↦ u ] → A
ouc = primSubOut


-- * Composition operation according to [CCHM 18].
-- When calling "comp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
-- compCCHM : ∀ {ℓ} (A : (i : I) → Set ℓ) (φ : I) (u : ∀ i → Partial (A i) φ) (a : A i0) → A i1

-- Note: this is not recommended to use, instead use the CHM
-- primitives! The reason is that these work with HITs and produce
-- fewer empty systems.


-- * Generalized transport and homogeneous composition [CHM 18].

-- When calling "transp A φ a" Agda makes sure that "A" is constant on "φ".
-- transp : ∀ {ℓ} (A : I → Set ℓ) (φ : I) (a : A i0) → A i1

-- When calling "hcomp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
-- hcomp : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : I → Partial A φ) (a : A) → A

private
  variable
    ℓ  : Level
    ℓ′ : I → Level
    A′ : Set ℓ
    φ : I

-- Homogeneous filling
hfill : ∀ (u : ∀ i → Partial φ A′)
          (u0 : A′ [ φ ↦ u i0 ]) (i : I) → A′
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → ouc u0 })
        (ouc u0)

-- Heterogeneous composition defined as in CHM
comp : ∀ (A : ∀ i → Set (ℓ′ i)) {φ : I}
         (u : ∀ i → Partial φ (A i))
         (u0 : A i0 [ φ ↦ u i0 ]) → A i1
comp A {φ = φ} u u0 =
  hcomp (λ i → λ { (φ = i1) → transp (λ j → A (i ∨ j)) i (u _ 1=1) })
        (transp A i0 (ouc u0))

-- Heterogeneous filling defined using comp
fill : ∀ (A : ∀ i → Set (ℓ′ i)) {φ : I}
         (u : ∀ i → Partial φ (A i))
         (u0 : A i0 [ φ ↦ u i0 ]) →
         ∀ i →  A i
fill A {φ = φ} u u0 i =
  comp (λ j → A (i ∧ j))
       (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                ; (i = i0) → ouc u0 })
       (inc {φ = φ ∨ (~ i)} (ouc {φ = φ} u0))

-- Direct definition of transport filler, note that we have to
-- explicitly tell Agda that the type is constant (like in CHM)
transpFill : ∀ (φ : I)
               (A : (i : I) → Set ℓ [ φ ↦ (λ _ → A′) ]) →
               (u0 : ouc (A i0)) →
               PathP (λ i → ouc (A i)) u0 (transp (λ i → ouc (A i)) φ u0)
transpFill φ A u0 i = transp (λ j → ouc (A (i ∧ j))) (~ i ∨ φ) u0
