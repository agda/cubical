{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.FGIdeal where
open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal renaming (generatedIdeal to generatedIdealCommRing)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal

private
  variable
    ℓ : Level

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) where
  open CommAlgebraStr (snd A)

  generatedIdeal : {n : ℕ} → FinVec (fst A) n → IdealsIn A
  generatedIdeal = generatedIdealCommRing (CommAlgebra→CommRing A)
