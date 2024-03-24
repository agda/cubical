{-# OPTIONS --safe  #-}

module Cubical.Tactics.WildCatSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Maybe

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.Tactics.WildCatSolver.Solvers
open import Cubical.Categories.Category

module WildCat-Solver ℓ ℓ' where

 WildCatWS : WildCatInstance ℓ ℓ'
 WildCatInstance.wildStr (WildCatWS) = WildCat ℓ ℓ'
 WildCatInstance.toWildCat WildCatWS x = x
 WildCatInstance.mbIsWildGroupoid WildCatWS = nothing

 private
  module WC-WS = WildCatInstance WildCatWS

 macro
  solveWildCat : R.Term → R.Term → R.TC Unit
  solveWildCat = WC-WS.solveW (R.def (quote WildCatWS) ( R.unknown v∷ R.unknown v∷ []))


module Cat-Solver ℓ ℓ' where

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

 Functor' : Category ℓ ℓ' → Category ℓ ℓ'  → Type (ℓ-max ℓ ℓ')
 Functor' x x₁ = WildFunctor (Cat→WildCat x) (Cat→WildCat x₁)

 private
  module C-WS = WildCatInstance CatWS

 macro
  solveCat : R.Term → R.Term → R.TC Unit
  solveCat = C-WS.solveW (R.def (quote CatWS) ( R.unknown v∷ R.unknown v∷ []))
