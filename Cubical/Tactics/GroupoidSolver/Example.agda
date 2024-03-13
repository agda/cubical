{-# OPTIONS --safe #-}

module Cubical.Tactics.GroupoidSolver.Example where

open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.Tactics.GroupoidSolver.Solver
open import Cubical.Data.Maybe

private
  variable
    ℓ ℓ' : Level



module exampleC (WC : WildCat ℓ ℓ') where
 -- open WildGroupoid WG
 open WildCat WC

 WC' : WildStr ℓ ℓ'
 WC' = WC , nothing

 module _ (x y z w v : ob) (p : Hom[ x , y ]) (q : Hom[ y , z ])
                           (r : Hom[ z , w ]) (s : Hom[ w , v ]) where


  pA pB pC : Hom[ x , v ]
  pA = (p ⋆ (id ⋆ q)) ⋆ (r ⋆ s)
  pB = (p ⋆ (q ⋆ ((r ⋆ id) ⋆ s))) ⋆ id
  pC = ((p ⋆ (id ⋆ q)) ⋆ r) ⋆ s


  pA=pB : pA ≡ pB
  pA=pB = solveWildCat WC'

  -- pA=pC : pA ≡ pC
  -- pA=pC = solveGroupoid WG'

  -- pB=pC : pB ≡ pC
  -- pB=pC = solveGroupoid WG'


module example (WG : WildGroupoid ℓ ℓ') where
 open WildGroupoid WG
 open WildCat wildCat

 WG' : WildStr ℓ ℓ'
 WG' = wildCat , just isWildGroupoid

 module _ (x y z w v : ob) (p p' : Hom[ x , y ]) (q q' : Hom[ y , z ])
                           (r : Hom[ w , z ]) (s : Hom[ w , v ]) where


  pA pB pC : Hom[ x , w ]
  pA = (p ⋆ (id ⋆ q)) ⋆ inv r
  pB = (p ⋆ ((q ⋆ (inv (inv r ⋆ ((s ⋆ inv s) ⋆ r)) ⋆ inv q)) ⋆ (q ⋆ id))) ⋆ (inv r ⋆ id)
  pC = (id ⋆ p') ⋆ (((q ⋆ inv q) ⋆ (inv p' ⋆ p)) ⋆ (q ⋆ (inv q ⋆ (q ⋆ inv r))))


  pA=pB : pA ≡ pB
  pA=pB = solveGroupoid WG'

  pA=pC : pA ≡ pC
  pA=pC = solveGroupoid WG'

  pB=pC : pB ≡ pC
  pB=pC = solveGroupoid WG'
