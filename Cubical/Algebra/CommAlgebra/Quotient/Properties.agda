{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.CommAlgebra.Quotient.Properties where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal hiding (IdealsIn)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Univalence
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.Quotient.Base

open import Cubical.Tactics.CommRingSolver

private variable
  ℓ ℓ' : Level

module _ {R : CommRing ℓ} {A : CommAlgebra R ℓ'} {I : IdealsIn R A} where

  ideal≡ToEquiv : {J : IdealsIn R A} → I ≡ J → CommAlgebraEquiv (A / I) (A / J)
  ideal≡ToEquiv {J = J} I≡J = pathToEquiv $ cong (λ K → A / K) I≡J
    where
      pathToEquiv : (A / I) ≡ (A / J) → CommAlgebraEquiv (A / I) (A / J)
      pathToEquiv = fst $ invEquiv $ CommAlgebraPath (A / I) (A / J)
