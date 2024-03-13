{-# OPTIONS --safe  #-}

module Cubical.Tactics.GroupSolver.Solver where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Unit
open import Cubical.Data.List as Li

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R

open import Cubical.Tactics.Reflection
open import Cubical.WildCat.Base
open import Cubical.Tactics.GroupoidSolver.Solver

open import Cubical.Algebra.Group

private
  variable
    ℓ : Level


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


macro
 solveGroup : R.Term → R.Term → R.TC Unit
 solveGroup g-t = groupoidSolverMain true (R.def (quote Group→WildGroupoid ) (g-t v∷ []))
