{-# OPTIONS --safe  #-}

module Cubical.Tactics.WildCatSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.Tactics.Reflection
open import Cubical.Tactics.WildCatSolver.Reflection
open import Cubical.Tactics.WildCatSolver.Solvers
open import Cubical.Categories.Category
open import Cubical.Categories.Functor


module WildCat-Solver ℓ ℓ' where


 mbWildFunctorApp : R.Term → Maybe (R.Term × R.Term)
 mbWildFunctorApp (R.def (quote WildFunctor.F-hom) t) = matchFunctorAppArgs t
 mbWildFunctorApp _ = nothing


 WildCatWS : WildCatInstance ℓ ℓ'
 WildCatInstance.wildStr (WildCatWS) = WildCat ℓ ℓ'
 WildCatInstance.toWildCat WildCatWS x = x
 WildCatInstance.mbIsWildGroupoid WildCatWS = nothing
 WildCatInstance.wildStrMor WildCatWS x y = WildFunctor x y
 WildCatInstance.toWildFunctor WildCatWS _ _ f = f
 WildCatInstance.mbFunctorApp WildCatWS = mbWildFunctorApp
 WildCatInstance.F-ty-extractSrc WildCatWS = extraxtWildFunSrc

 private
  module WC-WS = WildCatInstance WildCatWS

 macro
  solveWildCat : R.Term → R.Term → R.TC Unit
  solveWildCat = WC-WS.solveW (R.def (quote WildCatWS) ( R.unknown v∷ R.unknown v∷ []))


module Cat-Solver ℓ ℓ' where



 mbFunctorApp : R.Term → Maybe (R.Term × R.Term)
 mbFunctorApp (R.def (quote Functor.F-hom) t) = matchFunctorAppArgs t
 mbFunctorApp _ = nothing


 Cat→WildCat : Category ℓ ℓ' → WildCat ℓ ℓ'
 WildCat.ob (Cat→WildCat x) = Category.ob x
 WildCat.Hom[_,_] (Cat→WildCat x) = Category.Hom[_,_] x
 WildCat.id (Cat→WildCat x) = Category.id x
 WildCat._⋆_ (Cat→WildCat x) = Category._⋆_ x
 WildCat.⋆IdL (Cat→WildCat x) = Category.⋆IdL x
 WildCat.⋆IdR (Cat→WildCat x) = Category.⋆IdR x
 WildCat.⋆Assoc (Cat→WildCat x) = Category.⋆Assoc x


 CatWS : WildCatInstance ℓ ℓ'
 WildCatInstance.wildStr CatWS = Category ℓ ℓ'
 WildCatInstance.toWildCat CatWS = Cat→WildCat
 WildCatInstance.mbIsWildGroupoid CatWS = nothing
 WildCatInstance.wildStrMor CatWS x y = Functor x y
 WildCatInstance.toWildFunctor CatWS x y f =
   record { F-ob = F-ob ; F-hom = F-hom ; F-id = F-id ; F-seq = F-seq }
   where open Functor f
 WildCatInstance.mbFunctorApp CatWS = mbFunctorApp
 WildCatInstance.F-ty-extractSrc CatWS = extraxtWildFunSrc 
 private
  module C-WS = WildCatInstance CatWS

 macro
  solveCat : R.Term → R.Term → R.TC Unit
  solveCat = C-WS.solveW (R.def (quote CatWS) ( R.unknown v∷ R.unknown v∷ []))
