module Cubical.Algebra.CommAlgebra.Ideal where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
import Cubical.Algebra.CommRing.Ideal as CommRing
import Cubical.Algebra.CommRing.Ideal.Base


open import Cubical.Algebra.CommAlgebra.Base

open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' : Level

module _ (R : CommRing ℓ) (A : CommAlgebra R ℓ') where
  IdealsIn : Type _
  IdealsIn = CommRing.IdealsIn (fst A)

  open CommRingStr (A .fst .snd)

  makeIdeal : (I : A .fst .fst → hProp ℓ')
              → (+-closed : {x y : A .fst .fst} → x ∈ I → y ∈ I → (x + y) ∈ I)
              → (0-closed : 0r ∈ I)
              → (·-closedLeft : {x : A .fst .fst} → (r : A .fst .fst) → x ∈ I → r · x ∈ I)
              → IdealsIn
  makeIdeal = CommRing.makeIdeal {R = fst A}

  0Ideal : IdealsIn
  0Ideal = CommRing.CommIdeal.0Ideal (fst A)

  1Ideal : IdealsIn
  1Ideal = CommRing.CommIdeal.1Ideal (fst A)

open Cubical.Algebra.CommRing.Ideal.Base.CommIdeal using (isPropIsCommIdeal) public
