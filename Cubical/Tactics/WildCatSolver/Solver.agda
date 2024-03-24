{-# OPTIONS --safe  #-}

module Cubical.Tactics.WildCatSolver.Solver where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function as Fu
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.List as Li
open import Cubical.Data.Maybe as Mb


open import Cubical.HITs.Interval

-- open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.Reflection
open import Agda.Builtin.String

-- open import Cubical.WildCat.WGE
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.Algebra.Group

open import Cubical.Tactics.WildCatSolver.Solvers


module WildCat-Solver ℓ ℓ' where

 WildCatWS : WildStr ℓ ℓ'
 WildStr.wildStr (WildCatWS) = WildCat ℓ ℓ'
 WildStr.toWildCat WildCatWS = idfun _
 WildStr.mbIsWildGroupoid WildCatWS = nothing

 private 
  module WC-WS = WildStr WildCatWS

 macro
  solveWildCat : R.Term → R.Term → R.TC Unit
  solveWildCat = WC-WS.solveW (R.def (quote WildCatWS) ( R.unknown v∷ R.unknown v∷ []))
 
