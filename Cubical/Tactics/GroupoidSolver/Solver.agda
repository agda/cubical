{-# OPTIONS --safe  #-}

module Cubical.Tactics.GroupoidSolver.Solver where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R

open import Cubical.WildCat.Base

open import Cubical.Categories.Category

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.WildCatSolver.Solvers
open import Cubical.Tactics.WildCatSolver.Reflection
open import Cubical.Tactics.WildCatSolver.Solver

module WildGroupoid-Solver ℓ ℓ' where

 open import Cubical.WildCat.Functor

 mbWildFunctorApp : R.Term → Maybe (R.Term × R.Term)
 mbWildFunctorApp (R.def (quote WildFunctor.F-hom) t) = matchFunctorAppArgs t
 mbWildFunctorApp _ = nothing

 unWildCat : R.Term → R.TC R.Term
 unWildCat (R.def (quote WildGroupoid.wildCat) t) = matchFirstVarg t
 unWildCat _ = R.typeError [ R.strErr "unWildCat fail" ]



 GroupoidWS : WildCatInstance ℓ ℓ'
 WildCatInstance.wildStr GroupoidWS = WildGroupoid ℓ ℓ'
 WildCatInstance.toWildCat GroupoidWS = WildGroupoid.wildCat
 WildCatInstance.mbIsWildGroupoid GroupoidWS = just WildGroupoid.isWildGroupoid
 WildCatInstance.wildStrMor GroupoidWS _ _ = WildFunctor _ _
 WildCatInstance.toWildFunctor GroupoidWS _ _ f = f
 WildCatInstance.mbFunctorApp GroupoidWS = mbWildFunctorApp
 WildCatInstance.F-ty-extractSrc GroupoidWS =
   extraxtWildFunSrc >=> unWildCat
 WildCatInstance.extractWS GroupoidWS =
  WildCat-Solver.extrWS ℓ ℓ' >=> unWildCat

 private
  module WGPD-WS = WildCatInstance GroupoidWS

 macro

  solveWildGroupoid : R.Term → R.TC Unit
  solveWildGroupoid = WGPD-WS.solveW (R.def (quote GroupoidWS) ( R.unknown v∷ R.unknown v∷ [])) nothing

  solveWildGroupoid[_] : R.Term → R.Term → R.TC Unit
  solveWildGroupoid[ x ] = WGPD-WS.solveW (R.def (quote GroupoidWS) ( R.unknown v∷ R.unknown v∷ [])) (just x)


module Groupoid-Solver ℓ ℓ' where
 open import Cubical.Categories.Functor

 mbFunctorApp : R.Term → Maybe (R.Term × R.Term)
 mbFunctorApp (R.def (quote Functor.F-hom) t) = matchFunctorAppArgs t
 mbFunctorApp _ = nothing


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


 unCategory : R.Term → R.TC R.Term
 unCategory (R.def (quote GroupoidCat.category) t) = matchFirstVarg t
 unCategory _ = R.typeError [ R.strErr "unWildCat fail" ]


 GroupoidWS : WildCatInstance ℓ ℓ'
 WildCatInstance.wildStr GroupoidWS = GroupoidCat ℓ ℓ'
 WildCatInstance.toWildCat GroupoidWS = WildGroupoid.wildCat ∘ Groupoid→WildGroupoid
 WildCatInstance.mbIsWildGroupoid GroupoidWS =
  just (WildGroupoid.isWildGroupoid ∘ Groupoid→WildGroupoid)
 WildCatInstance.wildStrMor GroupoidWS x y = Functor (GroupoidCat.category x) (GroupoidCat.category y)
 WildCatInstance.toWildFunctor GroupoidWS x y f =
   record { F-ob = F-ob ; F-hom = F-hom ; F-id = F-id ; F-seq = F-seq }
   where open Functor f
 WildCatInstance.mbFunctorApp GroupoidWS = mbFunctorApp
 WildCatInstance.F-ty-extractSrc GroupoidWS =
   extraxtWildFunSrc >=> unCategory
 WildCatInstance.extractWS GroupoidWS =
   Cat-Solver.extrWS ℓ ℓ' >=> unCategory
 private
  module GPD-WS = WildCatInstance GroupoidWS

 macro
  solveWildGroupoid : R.Term → R.TC Unit
  solveWildGroupoid = GPD-WS.solveW (R.def (quote GroupoidWS) ( R.unknown v∷ R.unknown v∷ [])) nothing

  solveWildGroupoid[_] : R.Term → R.Term → R.TC Unit
  solveWildGroupoid[ x ] = GPD-WS.solveW (R.def (quote GroupoidWS) ( R.unknown v∷ R.unknown v∷ [])) (just x)

