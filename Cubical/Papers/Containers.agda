{-
Please do not move this file. Changes should only be made if
necessary.

This file contains pointers to the code examples and main results from
the paper:

Formalising inductive and coinductive containers,

-}

-- The "--safe" flag ensures that there are no postulates or
-- unfinished goals
{-# OPTIONS --safe --cubical --guardedness #-}

module Cubical.Papers.Containers where

-- 2
open import Cubical.Data.Unit                               as UnitType
open import Cubical.Data.Empty                              as EmptyType
open import Cubical.Data.Nat as Nat hiding (isEven)
open import Cubical.Codata.Stream                           as StreamType
open StreamType.Equality≅Bisimulation renaming (bisim to id)
open import Cubical.Foundations.Prelude                     as Foundations

open import Cubical.Data.W.W                                as W-Type
open import Cubical.Codata.M.MRecord                        as M-Type

open import Cubical.Data.Containers.Base                    as Container

-- 3
open import Cubical.Data.Containers.Algebras                as ContAlg
open import Cubical.Codata.Containers.Coalgebras            as ContCoAlg

-- 4
open import Cubical.Data.Containers.InductiveContainers     as IndCon
open import Cubical.Codata.Containers.CoinductiveContainers as CoIndCon

-- Unit type:
open UnitType renaming (Unit to ⊤)

-- Empty type:
open EmptyType using (⊥)

-- Natural numbers:
open Nat using (ℕ)

-- Σ-type:
-- omitted (we use a primitive version)

-- Streams
open StreamType using (Stream)

-- isEven, isEven+
isEven : ℕ → Type
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc n)) = isEven n

isEven+ : (n : ℕ) → isEven n → isEven (2 + n)
isEven+ n p = p

-- The interval type
open Foundations using (I ; _∧_ ; _∨_ ; ~_ ; i0 ; i1)

-- The path type
open Foundations using (_≡_)

-- refl and ⁻¹
open Foundations using (refl ; sym)

-- hcomp
open Foundations using (hcomp)

-- construction of top
module _ {A : Type} {x y z w : A} {p : x ≡ z} {q : x ≡ y} {r : y ≡ w}
  where
  top : z ≡ w
  top i = hcomp (λ j → λ {(i = i0) → p j ;
                           (i = i1) → r j})
                (q i)

-- transport and subst
open Foundations using (transport ; subst)

-- funExt
open Foundations using (funExt)

-- bisimulation and identity type of streams
open StreamType.Equality≅Bisimulation
  using (_≈_) renaming (bisim to id)


-- 2.2 The W-type and the M-type

-- The W-type
open W-Type using (W)

-- The M-type
open M-Type using (M)

-- MCoind
open M-Type using (MCoind)

-- 2.3 Containers
-- Definition 3
open Container using (GenContainer)

-- Definitions 4 and 5
-- Omitted (not used explicitly in formalisation)


---- 3 Setting up ----
-- Fixed points:
open ContAlg.Algs using (FixedPoint)

-- WAlg
open ContAlg.Algs using (WAlg)

-- MAlg
open ContCoAlg.Coalgs using (MAlg)

-- Pos
open ContAlg.Algs using (Pos)

-- Definition 6
-- Omitted (used implicitly)

-- Lemma 7
open ContAlg.Algs using (PosIndFun)


---- 4 Fixed points ----
-- Theorem 8
open IndCon using (into ; α̅ ; α̅Comm ; α̅Unique)

-- Theorem 9
open CoIndCon using (β̅Unique)

-- Lemma 10
open CoIndCon.β1.β2 using (β̅)

-- Lemma 11 (fstEq and sndEq)
open CoIndCon using (fstEq ; sndEq)

-- Lemma 12
open CoIndCon using (preFstEqId)
