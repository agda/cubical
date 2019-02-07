{-

This file contains:

- Definition of set quotients

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SetQuotients.Base where

open import Cubical.Foundations.HLevels
open import Cubical.Core.Prelude


-- Set quotients as a higher inductive type:
data _/_ {ℓ} (A : Set ℓ) (R : A → A → hProp {ℓ}) : Set ℓ where
  [_] : (a : A) → A / R
  eq/ : (a b : A) → (r : fst (R a b)) → [ a ] ≡ [ b ]
  squash/ : (x y : A / R) → (p q : x ≡ y) → p ≡ q
