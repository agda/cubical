{-
  This is just for convience and can be used to quickly set up notation for
  a commutative algebra.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommAlgebra.Base

module Cubical.Algebra.CommAlgebra.Notation where

open CommAlgebraStr ⦃...⦄ public
open CommRingStr ⦃...⦄ public

module InstancesForCAlg {ℓ ℓ' : Level} {R : CommRing ℓ} (A : CommAlgebra R ℓ') where

  instance
    baseRingStr  : CommRingStr ⟨ R ⟩
    baseRingStr  = R .snd
    ringStrOnAlg : CommRingStr ⟨ A ⟩ₐ
    ringStrOnAlg = CommAlgebra→CommRingStr A
    algStr       : CommAlgebraStr ⟨ A ⟩ₐ
    algStr       = CommAlgebra→CommAlgebraStr A
