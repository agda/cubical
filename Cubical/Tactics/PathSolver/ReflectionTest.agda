{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.ReflectionTest where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.List as Li
open import Cubical.Data.Maybe as Mb


open import Cubical.HITs.Interval

open import Cubical.Relation.Nullary

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.WildCatSolver.Reflection
open import Cubical.Tactics.Reflection
open import Agda.Builtin.String



module Test1 where

 module _ (n : ℕ) where
  data A : Type where
   a aa : A
   p : a ≡ aa

 macro
  unquoteA : R.Term → R.TC Unit
  unquoteA hole = do
   ty ← R.withNormalisation true $  R.inferType hole >>= wait-for-type
   final ← R.checkType (R.def (quote refl) []) ty >>= R.normalise 
   R.unify hole final
     -- (R∙ (R.def (quote refl) []) (R.def (quote refl) []))

 a' : Path (Path (A 3) a aa) (refl ∙ p) (refl ∙ p)
 a' = unquoteA
