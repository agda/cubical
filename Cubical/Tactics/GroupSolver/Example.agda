{-# OPTIONS --safe #-}

module Cubical.Tactics.GroupSolver.Example where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Group
open import Cubical.Tactics.GroupSolver.Solver
open import Cubical.Data.List

open import Cubical.WildCat.Functor

private
  variable
    ℓ : Level



module example (G G* G○ : Group ℓ)
               (F* : GroupHom' G* G)
               (F○ : GroupHom' G○ G*)
                where


 open Group-Solver ℓ


 open GroupStr (snd G)

 open WildFunctor

 module * where
  open GroupStr (snd G*) public

 module ○ where
  open GroupStr (snd G○) public



 module T1 (p p' q r : fst G ) where


   pA pB : fst G
   pA = ((((((1g · p') · q) · (inv q)) · (inv p')) · p) · q) · r
   pB = ((1g · p) · q) · r

   pA≡pB : pA ≡ pB
   pA≡pB = solveGroup (G ∷ [])
             
            
 
 module T2 p p' q r s t u where


  lhs rhs : fst G
  lhs = (p · p') · (inv p' · (F* ⟪ (((*.inv q) *.· r) *.· F○ ⟪ ○.inv t ⟫ *.·
              (*.inv (F○ ⟪ s ○.· s ⟫) *.· F○ ⟪ u ⟫ )) ⟫ ))
            
  rhs = inv (F* ⟪ q ⟫ · inv p) · (F* ⟪ r ⟫) ·
          (comp-WildFunctor F○ F*) ⟪ ○.inv (s ○.· s ○.· t) ○.· u ⟫


  lhs≡rhs : lhs ≡ rhs
  lhs≡rhs = solveGroup (G ∷ G* ∷ G○ ∷ [])
