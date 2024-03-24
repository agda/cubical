{-# OPTIONS --safe #-}

module Cubical.Tactics.WildCatSolver.Example where

open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.Tactics.WildCatSolver.Solver
open import Cubical.Data.List

open import Cubical.WildCat.Functor

private
  variable
    ℓ ℓ' : Level

module exampleC (WC WC* : WildCat ℓ ℓ')
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
  pA=pB = solveWildCat (WC ∷ WC* ∷ []) 

  pB=pC : pB ≡ pC
  pB=pC = solveWildCat (WC ∷ WC* ∷ [])



-- -- module example (WG WG* : WildGroupoid ℓ ℓ')
-- --                (F : WildFunctor
-- --                     (WildGroupoid.wildCat WG*)
-- --                     (WildGroupoid.wildCat WG))
-- --                 where

-- --  module WildStrGPD = WildStr (GroupoidWS {ℓ} {ℓ'}) 

-- --  -- open WildStrGPD using
-- --  --   (testInferExpr; solveNoInvs; solveW)

-- --  open WildGroupoid WG
-- --  open WildCat wildCat

-- --  open WildFunctor


-- --  module * where
-- --   open WildCat (WildGroupoid.wildCat WG*) public
-- --   open WildGroupoid WG* public

-- --  -- module T1 x y z w
-- --  --          (p : Hom[ x , y ])
-- --  --          (q : Hom[ y , z ])
-- --  --          (r : Hom[ z , w ]) where


-- --  --  pA pB : Hom[ x , w ]
-- --  --  pA = p ⋆ (q ⋆ r)
-- --  --  pB = (p ⋆ q) ⋆ r

-- --  --  -- pF : 

-- --  --  pXX : Hom[ x , x ]
-- --  --  pXX = id


-- --  --  tryTestOp : Unit
-- --  --  tryTestOp = testTryOp GroupoidWS WG pA

-- --  --  tryTestId : Unit
-- --  --  tryTestId = testTryId GroupoidWS WG pXX

-- --  --  pACase : FuCases WG pA
-- --  --  pACase = p FuCases.⋆FE (q ⋆ r)


-- --  module T1 x y z w
-- --           (p p' : Hom[ x , y ])
-- --           (q : Hom[ y , z ])
-- --           (r : Hom[ z , w ]) where


-- --    -- pA pB : Hom[ x , x ]
-- --    -- pA = (p ⋆ inv p)
-- --    -- pB = id

-- --    -- pA≡pB : pA ≡ pB
-- --    -- pA≡pB = {!solveW GroupoidWS (WG ∷ WG* ∷ [])!}


-- --    pA pB : Hom[ x , w ]
-- --    pA = ((((((id ⋆ p') ⋆ q) ⋆ (inv q)) ⋆ (inv p')) ⋆ p) ⋆ q) ⋆ r
-- --    -- pA = ((((((id ⋆ p))) ⋆ (inv p)) ⋆ p) ⋆ q) ⋆ r
-- --    pB = ((id ⋆ p) ⋆ q) ⋆ r

-- --    pA≡pB : pA ≡ pB
-- --    pA≡pB = WildStrGPD.solveW GroupoidWS (WG ∷ WG* ∷ [])
             
            
 
-- --  module T2 x y z w
-- --           (p : Hom[ x , F ⟅ y ⟆ ])
-- --           (p' : Hom[ F ⟅ y ⟆ , x ])
-- --           (q : *.Hom[ z , y ])
-- --           (r : *.Hom[ z , w ]) where


-- --   pA : Hom[ F ⟅ y ⟆ , F-ob F w ]
-- --   pA = F-hom F ((*.inv q) *.⋆ r)
-- --   pB pB' pB'' : Hom[ x , F ⟅ w ⟆ ]
-- --   pB = (p ⋆ (F-hom F ((*.inv q) *.⋆ r)))
-- --   pB'' = (p ⋆ p') ⋆ (inv p' ⋆ (F-hom F ((*.inv q) *.⋆ r)))
-- --   pB' = inv ((F-hom F q) ⋆ inv p) ⋆ (F-hom F r)  


-- --   pB''≡pB' : pB'' ≡ pB'
-- --   pB''≡pB' = WildStrGPD.solveW GroupoidWS (WG ∷ WG* ∷ [])






-- -- -- module example (WG WG* : WildGroupoid ℓ ℓ')
-- -- --               (F : WildFunctor (WildGroupoid.wildCat WG*) (WildGroupoid.wildCat WG)) where
-- -- --  open WildGroupoid WG
-- -- --  open WildCat wildCat



-- -- --  module * where
-- -- --   open WildCat (WildGroupoid.wildCat WG*) public
-- -- --   open WildGroupoid WG* public

-- -- --  module _ x v y z w
-- -- --           (p p' : Hom[ x , F ⟅ y ⟆ ])
-- -- --           (q q' : *.Hom[ y , z ])
-- -- --           (r : *.Hom[ w , z ])
-- -- --           (s : Hom[ F ⟅ w ⟆ , v ]) where


-- -- --   pA pB pC : Hom[ x , v ]
-- -- --   pA = (p ⋆ (id ⋆ F ⟪ q *.⋆ *.inv q' ⟫)) ⋆ (F ⟪ q' *.⋆ (*.inv r) ⟫ ⋆ s)
-- -- --   pB = ((p ⋆ F  ⟪ q *.⋆ (*.inv (*.inv r *.⋆ r) *.⋆ *.inv q)⟫)
-- -- --             ⋆ F ⟪ q *.⋆ *.id ⟫) ⋆ ((inv (F ⟪ r ⟫ ⋆ id)) ⋆ s)

-- -- --   pC = p' ⋆ (inv p' ⋆ (p ⋆ (F ⟪ q *.⋆ (*.inv r) ⟫ ⋆ s)))

-- -- --   pA=pB : pA ≡ pB
-- -- --   pA=pB = solveGroupoid WG WG* 

-- -- --   pA=pC : pA ≡ pC
-- -- --   pA=pC = solveGroupoid WG WG* 


