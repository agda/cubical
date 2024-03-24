{-# OPTIONS --safe #-}

module Cubical.Tactics.GroupoidSolver.Example where

open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.Tactics.GroupoidSolver.Solver
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Categories.Category
open import Cubical.WildCat.Functor

private
  variable
    ℓ ℓ' : Level

module example (WG WG* : WildGroupoid ℓ ℓ')
               (F : WildFunctor
                    (WildGroupoid.wildCat WG*)
                    (WildGroupoid.wildCat WG))
                where

 open WildGroupoid-Solver ℓ ℓ'


 open WildGroupoid WG
 open WildCat wildCat

 open WildFunctor


 module * where
  open WildCat (WildGroupoid.wildCat WG*) public
  open WildGroupoid WG* public


 module T1 x y z w
          (p p' : Hom[ x , y ])
          (q : Hom[ y , z ])
          (r : Hom[ z , w ]) where


   pA pB : Hom[ x , w ]
   pA = ((((((id ⋆ p') ⋆ q) ⋆ ((inv q) ⋆ id)) ⋆ (inv p')) ⋆ p) ⋆ q) ⋆ r
   pB = p ⋆ (q ⋆ r)

   pA≡pB : pA ≡ pB
   pA≡pB = solveWildGroupoid (WG ∷ WG* ∷ [])



 module T2 x y z w
          (p : Hom[ x , F ⟅ y ⟆ ])
          (p' : Hom[ F ⟅ y ⟆ , x ])
          (q : *.Hom[ z , y ])
          (r : *.Hom[ z , w ]) where


  lhs rhs : Hom[ x , F ⟅ w ⟆ ]
  lhs = (p ⋆ p') ⋆ (inv p' ⋆ (F ⟪ (*.inv q) *.⋆ r ⟫))
  rhs = inv (F ⟪ q ⟫ ⋆ inv p) ⋆ F ⟪ r ⟫


  lhs≡rhs : lhs ≡ rhs
  lhs≡rhs = solveWildGroupoid (WG ∷ WG* ∷ [])


 module T3 (obs : ℕ → ob)
          (homs : ∀ x y → ℕ → Hom[ obs x , obs y ])
          where

  lhs rhs : Hom[ obs 1 , obs 5 ]
  lhs = homs _ 2 1 ⋆ (homs _ _ 2 ⋆ (homs 3 5 2 ⋆ (homs _ 6 3 ⋆ inv (homs _ 6 3))))
  rhs = ((homs _ 2 1 ⋆ homs _ _ 2) ⋆ id) ⋆ homs 3 5 2


  lhs≡rhs : lhs ≡ rhs
  lhs≡rhs = solveWildGroupoid (WG ∷ [])


module exampleGpd (G G* : GroupoidCat ℓ ℓ')
               (F : WildFunctor
                    (WildGroupoid.wildCat (Groupoid-Solver.Groupoid→WildGroupoid _ _ G*))
                    (WildGroupoid.wildCat (Groupoid-Solver.Groupoid→WildGroupoid _ _ G)))
                where

 open Groupoid-Solver ℓ ℓ'



 module * where
   open GroupoidCat G* public
   open Category category public

 open GroupoidCat G
 open Category category


 module T1 x y z w
          (p : Hom[ x , F ⟅ y ⟆ ])
          (p' : Hom[ F ⟅ y ⟆ , x ])
          (q : *.Hom[ z , y ])
          (r : *.Hom[ z , w ]) where


  lhs rhs : Hom[ x , F ⟅ w ⟆ ]
  lhs = (p ⋆ p') ⋆ (p' ⁻¹ ⋆ (F ⟪ (q *.⁻¹) *.⋆ r ⟫))
  rhs = (F ⟪ q ⟫ ⋆  p ⁻¹) ⁻¹ ⋆ F ⟪ r ⟫


  lhs≡rhs : lhs ≡ rhs
  lhs≡rhs = solveWildGroupoid (G ∷ G* ∷ [])
