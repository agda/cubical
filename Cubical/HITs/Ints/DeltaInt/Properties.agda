{-# OPTIONS --cubical --safe #-}

{-

This file defines

deltaIntSec : ∀ b → toInt (fromInt b) ≡ b
succPred : ∀ n → succ (pred n) ≡ n
predSucc : ∀ n → pred (succ n) ≡ n

and proved DeltaInt ≡ DeltaInt by the above functions

succPredEq : DeltaInt ≡ DeltaInt

along with some interval-relevant lemmas

cancelDiamond  : ∀ a b i → cancel a b i ≡ cancel (suc a) (suc b) i
cancelTriangle : ∀ a b i → a ⊖ b ≡ cancel a b i

-}

module Cubical.HITs.Ints.DeltaInt.Properties where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat hiding (zero)
open import Cubical.Data.Int hiding (abs; sgn; _+_)
open import Cubical.HITs.Ints.DeltaInt.Base

deltaIntSec : ∀ b → toInt (fromInt b) ≡ b
deltaIntSec (pos n) = refl
deltaIntSec (negsuc n) = refl

cancelDiamond : ∀ a b i → cancel a b i ≡ cancel (suc a) (suc b) i
cancelDiamond a b i j = hcomp (λ k → λ
  { (i = i0) → cancel a b j
  ; (i = i1) → cancel (suc a) (suc b) (j ∧ k)
  ; (j = i0) → cancel a b i
  ; (j = i1) → cancel (suc a) (suc b) (i ∧ k)
  }) (cancel a b (i ∨ j))

cancelTriangle : ∀ a b i → a ⊖ b ≡ cancel a b i
cancelTriangle a b i j = hcomp (λ k → λ
  { (i = i0) → a ⊖ b
  ; (i = i1) → cancel a b (j ∧ k)
  ; (j = i0) → a ⊖ b
  ; (j = i1) → cancel a b (i ∧ k)
  }) (a ⊖ b)

{-
If you wish to prove this, we wish you good luck.

deltaIntRet : ∀ a → fromInt (toInt a) ≡ a
deltaIntRet (x ⊖ 0) = refl
deltaIntRet (0 ⊖ suc y) = refl
deltaIntRet (suc x ⊖ suc y) = deltaIntRet (x ⊖ y) ∙ cancel x y
-- a ⊖ 0 ≡ cancel a 0 i
deltaIntRet (cancel a 0 i) = {!cancelTriangle a 0 i!}
deltaIntRet (cancel 0 (suc b) i) = {!cancelTriangle 0 (suc b) i!}
deltaIntRet (cancel (suc a) (suc b) i) = deltaIntRet (cancel a b i) ∙ cancelDiamond a b i

DeltaInt≡Int : DeltaInt ≡ Int
DeltaInt≡Int = isoToPath (iso toInt fromInt deltaIntSec deltaIntRet)
-}

succPred : ∀ n → succ (pred n) ≡ n
succPred (x ⊖ y) i = cancel x y (~ i)
-- cancel (suc a) (suc b) i ≡ cancel a b i
succPred (cancel a b i) = sym (cancelDiamond a b i)

predSucc : ∀ n → pred (succ n) ≡ n
predSucc (x ⊖ y) = succPred (x ⊖ y)
predSucc (cancel a b i) = succPred (cancel a b i)

succPredEq : DeltaInt ≡ DeltaInt
succPredEq = isoToPath (iso succ pred succPred predSucc)
