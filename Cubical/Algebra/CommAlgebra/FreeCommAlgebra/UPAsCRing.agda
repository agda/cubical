{-# OPTIONS --safe #-}

module Cubical.Algebra.CommAlgebra.FreeCommAlgebra.UPAsCRing where
{-
  This file contains
  * The universal property of the free commutative algebra/polynomial ring
    as a commutative ring.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function hiding (const)
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.HITs.SetTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra.Properties
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.Module using (module ModuleTheory)

open import Cubical.Data.Empty
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' : Level


module UniversalPropertyAsCommRing
         {R : CommRing ℓ} (I : Type ℓ')
         (S : CommRing ℓ'') (f : CommRingHom R S)
         (φ : I → ⟨ S ⟩)
         where
  inducedMap : ⟨ R [ I ]ᵣ ⟩ → ⟨ S ⟩
  inducedMap = Theory.inducedMap (CommAlgChar.toCommAlg R (S , f)) φ
