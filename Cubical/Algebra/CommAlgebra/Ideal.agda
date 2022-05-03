{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Ideal where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal renaming (IdealsIn to IdealsInCommRing;
                                                     makeIdeal to makeIdealCommRing)
open import Cubical.Algebra.CommAlgebra

private
  variable
    ℓ : Level

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) where
  IdealsIn : Type _
  IdealsIn = IdealsInCommRing (CommAlgebra→CommRing A)

  open CommAlgebraStr (snd A)

  makeIdeal : (I : fst A → hProp ℓ)
              → (+-closed : {x y : fst A} → x ∈ I → y ∈ I → (x + y) ∈ I)
              → (0-closed : 0a ∈ I)
              → (·-closedLeft : {x : fst A} → (r : fst A) → x ∈ I → r · x ∈ I)
              → IdealsIn
  makeIdeal = makeIdealCommRing {R = CommAlgebra→CommRing A}
