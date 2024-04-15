{-# OPTIONS --safe  #-}

module Cubical.Tactics.GroupSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R

open import Cubical.WildCat.Base



open import Cubical.Tactics.WildCatSolver.Reflection

open import Cubical.WildCat.Functor
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.WildCatSolver.Solvers


module _ {ℓ} where

 module _ (G : Group ℓ) where
  open GroupStr (snd G)
  Group→WildGroupoid : WildGroupoid ℓ-zero ℓ
  WildCat.ob (WildGroupoid.wildCat Group→WildGroupoid) = Unit
  WildCat.Hom[_,_] (WildGroupoid.wildCat Group→WildGroupoid) _ _ = ⟨ G ⟩
  WildCat.id (WildGroupoid.wildCat Group→WildGroupoid) = 1g
  WildCat._⋆_ (WildGroupoid.wildCat Group→WildGroupoid) = _·_
  WildCat.⋆IdL (WildGroupoid.wildCat Group→WildGroupoid) = ·IdL
  WildCat.⋆IdR (WildGroupoid.wildCat Group→WildGroupoid) = ·IdR
  WildCat.⋆Assoc (WildGroupoid.wildCat Group→WildGroupoid) _ _ _ = sym (·Assoc _ _ _)
  wildIsIso.inv' (WildGroupoid.isWildGroupoid Group→WildGroupoid f) = inv f
  wildIsIso.sect (WildGroupoid.isWildGroupoid Group→WildGroupoid f) = ·InvL f
  wildIsIso.retr (WildGroupoid.isWildGroupoid Group→WildGroupoid f) = ·InvR f

module _ ℓ where

 mbGroupHomApp : R.Term → Maybe (R.Term × R.Term)
 mbGroupHomApp (R.def (quote fst) t) = match2Vargs' t
 mbGroupHomApp _ = nothing


 groupHomTrmSrc : R.Term → R.TC R.Term
 groupHomTrmSrc (R.def (quote Σ) t) = do
   (fun , isGrpHomTrm) ← match2Vargs t
   funDom ← matchPiDom fun
   unFst funDom
 groupHomTrmSrc t = R.typeError $ (R.strErr "groupHomTrmSrc fail: ") ∷ (getConTail t)


 GroupWS : WildCatInstance ℓ-zero ℓ
 WildCatInstance.wildStr GroupWS = Group ℓ
 WildCatInstance.toWildCat GroupWS = WildGroupoid.wildCat ∘ Group→WildGroupoid
 WildCatInstance.mbIsWildGroupoid GroupWS = just (WildGroupoid.isWildGroupoid ∘ Group→WildGroupoid)
 WildCatInstance.wildStrMor GroupWS = GroupHom
 WildCatInstance.toWildFunctor GroupWS _ _ (f , isGHom) =
   record { F-ob = _ ; F-hom = f ; F-id = pres1 ; F-seq = pres· }
   where open IsGroupHom isGHom
 WildCatInstance.mbFunctorApp GroupWS = mbGroupHomApp
 WildCatInstance.F-ty-extractSrc GroupWS = groupHomTrmSrc
 WildCatInstance.extractWS GroupWS = unFst
 private
  module GRP-WS = WildCatInstance GroupWS


 module Group-Solver (no-norm-defs : List R.Name) where

  macro
   solveGroup[_] : R.Term → R.Term → R.TC Unit
   solveGroup[ x ] y =
     R.withReduceDefs (false , no-norm-defs) (GRP-WS.solveW (R.def (quote GroupWS) ( R.unknown v∷ [])) (just x) y)

   solveGroup : R.Term → R.TC Unit
   solveGroup y =
     R.withReduceDefs (false , no-norm-defs) (GRP-WS.solveW (R.def (quote GroupWS) ( R.unknown v∷ [])) nothing y)

