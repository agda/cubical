{-# OPTIONS --safe #-}

module Cubical.Tactics.WildCatSolver.Example where

open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.Tactics.WildCatSolver.Solver
open import Cubical.Data.List

private
  variable
    ℓ ℓ' : Level


module exampleWC where
 open import Cubical.WildCat.Functor

 module _ (WC WC* : WildCat ℓ ℓ')
                 (F : WildFunctor WC* WC) where

  open WildCat WC
  module * = WildCat WC*

  module _ x y z w v
           (p : Hom[ x , F ⟅ y ⟆ ])
           (q : *.Hom[ y , z ])
           (r : *.Hom[ z , w ])
           (s : Hom[ F ⟅ w ⟆ , v ]) where


   pA pB pC : Hom[ x , v ]
   pA = (p ⋆ (id ⋆ F ⟪ q ⟫)) ⋆ (F ⟪ r ⟫ ⋆ s)
   pB = ((p ⋆ F ⟪ q *.⋆ (*.id *.⋆ *.id) ⟫ ) ⋆  F ⟪ *.id *.⋆ *.id ⟫) ⋆ (( F ⟪ r ⟫ ⋆ id) ⋆ s)
   pC = p ⋆ (F ⟪ q *.⋆ r ⟫ ⋆ s)

   open WildCat-Solver ℓ ℓ'

   pA=pB : pA ≡ pB
   pA=pB = solveWildCat
   
   pB=pC : pB ≡ pC
   pB=pC = solveWildCat


module exampleC ℓ ℓ' where
 open import Cubical.Categories.Category
 open import Cubical.Categories.Functor

 open Cat-Solver ℓ ℓ'


 module _ (C C* : Category ℓ ℓ')  (F : Functor C* C) where


  open Category C
  module * = Category C*

  module E1 x y z w v
           (p : Hom[ x , y ])
           (q : Hom[ y , z ])
           (r : Hom[ z , w ])
           (s : Hom[ w , v ]) where


   pA pB pC : Hom[ x , v ]
   pA = (p ⋆ (id ⋆ q)) ⋆ (r ⋆ s)
   pB = (((p ⋆ q) ⋆ (id ⋆ id) ) ⋆ id ⋆ id) ⋆ (( r ⋆ id) ⋆ s)
   pC = p ⋆ (q ⋆ r ⋆ s)


   pA=pB : pA ≡ pB
   pA=pB = solveCat

   pB=pC : pB ≡ pC
   pB=pC = solveCat

  module E2 x y z w v
           (p : Hom[ x , F ⟅ y ⟆ ])
           (q : *.Hom[ y , z ])
           (r : *.Hom[ z , w ])
           (s : Hom[ F ⟅ w ⟆ , v ]) where





   -- pA pB : Hom[ F ⟅ y ⟆ , F ⟅ w ⟆ ]
   -- pA = F ⟪ q *.⋆ r ⟫
   -- pB = F ⟪ q ⟫ ⋆ F ⟪ r ⟫

   -- pA=pB : pA ≡ pB
   -- pA=pB = solveCat (C ∷ C* ∷ [])


   pA pB pC : Hom[ x , v ]
   pA = (p ⋆ (id ⋆ F ⟪ q ⟫)) ⋆ (F ⟪ r ⟫ ⋆ s)
   pB = ((p ⋆ F ⟪ q *.⋆ (*.id *.⋆ *.id) ⟫ ) ⋆  F ⟪ *.id *.⋆ *.id ⟫) ⋆ (( F ⟪ r ⟫ ⋆ id) ⋆ s)
   pC = p ⋆ (F ⟪ q *.⋆ r ⟫ ⋆ s)

   pA=pB : pA ≡ pB
   pA=pB = solveCat

   pB=pC : pB ≡ pC
   pB=pC = solveCat

