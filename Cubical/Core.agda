{-

This file documents and export the main primitives of Cubical Agda. It
also defines some basic derived operations (composition and filling).


It should *not* depend on the Agda standard library.

-}
{-# OPTIONS --cubical #-}
module Cubical.Core where

open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           -- TODO change to emptySystem in src/full
           ; isOneEmpty     to empty
           ; primComp to compCCHM  -- This should not be used
           ; primHComp to hcomp
           ; primTransp to transp
           ; itIsOne    to 1=1 )

open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.Sub public
  renaming ( Sub to _[_↦_]
           ; primSubOut to ouc )
open import Agda.Primitive public
  using    ( Level )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max )

-- This files document the Cubical Agda primitives.
-- The primitives themselves are bound by the agda files imported above.

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


-- Non dependent path type.

Path : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
Path A a b = PathP (λ _ → A) a b

-- PathP (\ i → A) x y gets printed as x ≡ y when A does not mention i.
--  _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
--  _≡_ {A = A} = PathP (λ _ → A)


-- * @IsOne r@ represents the constraint "r = i1".
-- Often we will use "φ" for elements of I, when we intend to use them
-- with IsOne (or Partial[P]).
-- IsOne : I → Set

-- i1 is indeed equal to i1.
-- 1=1 : IsOne i1


-- * Types of partial elements, and their dependent version.

-- "Partial A φ" is a special version of "IsOne φ → A" with a more
-- extensional judgmental equality.
-- "PartialP φ A" allows "A" to be defined only on "φ".

-- Partial : ∀ {l} → Set l → I → Setω
-- PartialP : ∀ {l} → (φ : I) → Partial (Set l) φ → Setω

-- Partial elements are introduced by pattern matching with (r = i0) or (r = i1) constraints, like so:

private
  sys : ∀ i → Partial Set₁ (i ∨ ~ i)
  sys i (i = i0) = Set
  sys i (i = i1) = Set → Set

-- It also works with pattern matching lambdas. (TODO link pattern matching lambda docs)
  sys' : ∀ i → Partial Set₁ (i ∨ ~ i)
  sys' i = \ { (i = i0) → Set
             ; (i = i1) → Set → Set
             }

-- When the cases overlap they must agree.
  sys2 : ∀ i j → Partial Set₁ (i ∨ (i ∧ j))
  sys2 i j = \ { (i = i1)          → Set
               ; (i = i1) (j = i1) → Set
               }

-- TODO recognize IsOne i0 as empty, then we can get rid of the empty system.
-- sys3 : Partial Set₁ i0
-- sys3 = \ { () }



-- * The empty System
-- empty : ∀ {a} {A : Partial (Set a) i0} → PartialP i0 A


-- * Composition operation according to [CCHM 18].
-- When calling "comp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
-- compCCHM : ∀ {l} (A : (i : I) → Set l) (φ : I) (u : ∀ i → Partial (A i) φ) (a : A i0) → A i1

-- Note: this is not recommended to use, instead use the CHM primitives!


-- * Generalized transport and homogeneous composition [CHM 18].
-- Used to support Higher Inductive Types.

-- When calling "transp A φ a" Agda makes sure that "A" is constant on "φ".
-- transp : ∀ {l} (A : (i : I) → Set l) (φ : I) (a : A i0) → A i1

-- When calling "hcomp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
-- hcomp : ∀ {l} (A : Set l) (φ : I) (u : I → Partial A φ) (a : A) → A

-- Homogeneous filling
hfill : ∀ {ℓ} (A : Set ℓ) {φ : I}
          (u : ∀ i → Partial A φ)
          (u0 : A [ φ ↦ u i0 ]) (i : I) → A
hfill A {φ = φ} u u0 i =
  hcomp A _
        (λ j → \ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → ouc u0 })
        (ouc u0)

-- Heterogeneous composition defined as in CHM
comp : ∀ {ℓ} (A : I → Set ℓ) {φ : I}
         (u : ∀ i → Partial (A i) φ)
         (u0 : A i0 [ φ ↦ u i0 ]) → A i1
comp A {φ = φ} u u0 =
  hcomp (A i1) _
        (\ i → \ { (φ = i1) → transp (\ j → A (i ∨ j)) i (u _ 1=1) })
        (transp A i0 (ouc u0))

-- Heterogeneous filling defined using comp
fill : ∀ {ℓ} (A : I → Set ℓ) {φ : I}
         (u : ∀ i → Partial (A i) φ)
         (u0 : A i0 [ φ ↦ u i0 ]) →
         PathP A (ouc u0) (comp A u u0)
fill A {φ = φ} u u0 i =
  comp (λ j → A (i ∧ j))
       (λ j → \ { (φ = i1) → u (i ∧ j) 1=1
                ; (i = i0) → ouc u0 })
       (inc {φ = φ ∨ (~ i)} (ouc {φ = φ} u0))

-- Direct definition of transport filler, note that we have to
-- explicitly tell Agda that the type is constant (like in CHM)
transpFill : ∀ {ℓ} {A' : Set ℓ} (φ : I)
               (A : (i : I) → Set ℓ [ φ ↦ (\ _ → A') ]) →
               (u0 : ouc (A i0)) →
               PathP (λ i → ouc (A i)) u0 (transp (λ i → ouc (A i)) φ u0)
transpFill φ A u0 i = transp (\ j → ouc (A (i ∧ j))) (~ i ∨ φ) u0
