{-# OPTIONS --safe #-}

module Cubical.Tactics.GroupSolver.Example where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Tactics.GroupSolver.Solver
open import Cubical.Data.List

private
  variable
    ℓ : Level

module example (G G* G○ : Group ℓ)
               (F* : GroupHom G* G)
               (F○ : GroupHom G○ G*)
                where


 open Group-Solver ℓ []


 open GroupStr (snd G)

 module * where
  open GroupStr (snd G*) public

 module ○ where
  open GroupStr (snd G○) public



 module T1 (p p' q r : fst G ) where


   pA pB : fst G
   pA = ((((((1g · p') · q) · (inv q)) · (inv p')) · p) · q) · r
   pB = ((1g · p) · q) · r

   pA≡pB : pA ≡ pB
   pA≡pB = solveGroup


 module T2 p p' q r s t u where


  lhs rhs : fst G
  lhs = p · (p · inv p) · inv p · (p' · inv p') · (p · p') ·
            (inv p' · (fst F* (((*.inv q) *.· r) *.· fst F○ (○.inv t) *.·
              (*.inv (fst F○ ( s ○.· s )) *.· fst F○ u )) ))

  rhs = inv (fst F* q · inv p) · (fst F* r) ·
          fst (compGroupHom F○ F*) (○.inv (s ○.· s ○.· t) ○.· u )


  lhs≡rhs : lhs ≡ rhs
  lhs≡rhs = solveGroup

module ℤexamples where
 open import Cubical.Data.Nat using (ℕ)
 open import Cubical.Algebra.Group.Instances.Int

 open GroupStr (snd ℤGroup)

 module _ k ([_]ᶻ : ℕ → fst ℤGroup) where


  open Group-Solver ℓ-zero
        (quote ℤGroup ∷ [ quote ℤHom ])


  lhs rhs : (fst ℤGroup)
  lhs = fst (ℤHom  k) ([ 1 ]ᶻ · [ 3 ]ᶻ)
  rhs = fst (ℤHom  k) [ 1 ]ᶻ · fst (ℤHom k) [ 3 ]ᶻ

  lhs≡rhs : lhs ≡ rhs
  lhs≡rhs = solveGroup[ ℤGroup ]
