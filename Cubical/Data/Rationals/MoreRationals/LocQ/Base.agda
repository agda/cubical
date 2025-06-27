{-# OPTIONS --safe #-}
module Cubical.Data.Rationals.MoreRationals.LocQ.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Relation.Nullary
open import Cubical.Data.Int as ℤ
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommRing.Localisation

ℤNonzeroℙ : ℙ ℤ
ℤNonzeroℙ n .fst = ¬ n ≡ 0
ℤNonzeroℙ n .snd = isProp¬ (n ≡ 0)