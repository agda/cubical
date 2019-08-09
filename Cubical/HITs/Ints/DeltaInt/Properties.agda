{-# OPTIONS --cubical --safe #-}

{-

This file defines

succPred : ∀ n → succ (pred n) ≡ n
predSucc : ∀ n → pred (succ n) ≡ n

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
  ; (i = i1) → cancel (suc a) (suc b) j
  ; (j = i0) → cancel a b i
  ; (j = i1) → cancel (suc a) (suc b) i
  }) (hcomp (λ k → λ
    { (i = i0) → cancel a b j
    ; (i = i1) → cancel (suc a) (suc b) (j ∧ k)
    ; (j = i0) → cancel a b i
    ; (j = i1) → cancel (suc a) (suc b) (i ∧ k)
    }) (cancel a b (i ∨ j)))

{-
If you wish to prove this, we wish you good luck.

deltaIntRet : ∀ a → fromInt (toInt a) ≡ a
deltaIntRet (x ⊖ 0) = refl
deltaIntRet (0 ⊖ suc y) = refl
deltaIntRet (suc x ⊖ suc y) = deltaIntRet (x ⊖ y) ∙ cancel x y
-- a ⊖ 0 ≡ cancel a 0 i
deltaIntRet (cancel a 0 i) j = {!cancel a 0 (i ∧ ~ j)!}
deltaIntRet (cancel 0 (suc b) i) = cancelHelper (suc b) i
  where
  cancelHelper : ∀ b i → 0 ⊖ b ≡ cancel 0 b i
  cancelHelper b i = {!b!}
deltaIntRet (cancel (suc a) (suc b) i) = deltaIntRet (cancel a b i) ∙ cancelHelper a b i
  where
  cancelHelper : ∀ a b i → cancel a b i ≡ cancel (suc a) (suc b) i
  cancelHelper a b i = {!!}

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

