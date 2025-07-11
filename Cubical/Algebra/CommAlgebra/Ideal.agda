{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Ideal where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal renaming (IdealsIn to IdealsInCommRing;
                                                     makeIdeal to makeIdealCommRing)
open import Cubical.Algebra.CommAlgebra.Base
-- open import Cubical.Algebra.Ring

open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' : Level

module _ (R : CommRing ℓ) (A : CommAlgebra R ℓ') where
  IdealsIn : Type _
  IdealsIn = IdealsInCommRing (fst A)

  open CommRingStr (A .fst .snd)

  makeIdeal : (I : A .fst .fst → hProp ℓ')
              → (+-closed : {x y : A .fst .fst} → x ∈ I → y ∈ I → (x + y) ∈ I)
              → (0-closed : 0r ∈ I)
              → (·-closedLeft : {x : A .fst .fst} → (r : A .fst .fst) → x ∈ I → r · x ∈ I)
              → IdealsIn
  makeIdeal = makeIdealCommRing {R = fst A}

  0Ideal : IdealsIn
  0Ideal = CommIdeal.0Ideal (fst A)

  1Ideal : IdealsIn
  1Ideal = CommIdeal.1Ideal (fst A)
