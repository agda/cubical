{-# OPTIONS --safe  #-}

module Cubical.Tactics.GroupoidSolver.Solver where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Maybe

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R

open import Cubical.WildCat.Base
open import Cubical.Categories.Category
open import Cubical.Tactics.WildCatSolver.Solvers
open import Cubical.Tactics.WildCatSolver.Solver

module WildGroupoid-Solver ℓ ℓ' where

 GroupoidWS : WildCatInstance ℓ ℓ'
 WildCatInstance.wildStr GroupoidWS = WildGroupoid ℓ ℓ'
 WildCatInstance.toWildCat GroupoidWS = WildGroupoid.wildCat
 WildCatInstance.mbIsWildGroupoid GroupoidWS = just WildGroupoid.isWildGroupoid

 private
  module WGPD-WS = WildCatInstance GroupoidWS

 macro
  solveWildGroupoid : R.Term → R.Term → R.TC Unit
  solveWildGroupoid = WGPD-WS.solveW (R.def (quote GroupoidWS) ( R.unknown v∷ R.unknown v∷ []))

module Groupoid-Solver ℓ ℓ' where


 Groupoid→WildGroupoid : GroupoidCat ℓ ℓ' → WildGroupoid ℓ ℓ'
 WildGroupoid.wildCat (Groupoid→WildGroupoid x) =
   Cat-Solver.Cat→WildCat _ _ (GroupoidCat.category x)
 WildGroupoid.isWildGroupoid (Groupoid→WildGroupoid x) f = wgi
   where

   open isIso (GroupoidCat.isGroupoidCat x f)

   wgi : wildIsIso f
   wildIsIso.inv' wgi = inv
   wildIsIso.sect wgi = sec
   wildIsIso.retr wgi = ret

 GroupoidWS : WildCatInstance ℓ ℓ'
 WildCatInstance.wildStr GroupoidWS = GroupoidCat ℓ ℓ'
 WildCatInstance.toWildCat GroupoidWS = WildGroupoid.wildCat ∘ Groupoid→WildGroupoid
 WildCatInstance.mbIsWildGroupoid GroupoidWS =
  just (WildGroupoid.isWildGroupoid ∘ Groupoid→WildGroupoid)

 private
  module GPD-WS = WildCatInstance GroupoidWS

 macro
  solveWildGroupoid : R.Term → R.Term → R.TC Unit
  solveWildGroupoid = GPD-WS.solveW (R.def (quote GroupoidWS) ( R.unknown v∷ R.unknown v∷ []))

