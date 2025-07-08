{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.CommAlgebra.FP.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Polynomials
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal


private
  variable
    ℓ ℓ' : Level

module _ (R : CommRing ℓ) where
  Polynomials : (n : ℕ) → CommAlgebra R ℓ
  Polynomials n = R [ Fin n ]ₐ

  record FinitePresentation : Type ℓ where
    no-eta-equality
    field
      n : ℕ
      m : ℕ
      relations : FinVec ⟨ Polynomials n ⟩ₐ m

    opaque
      ideal : IdealsIn R (Polynomials n)
      ideal = ⟨ relations ⟩[ Polynomials n ]

    opaque
      algebra : CommAlgebra R ℓ
      algebra = Polynomials n / ideal

      π : CommAlgebraHom (Polynomials n) algebra
      π = quotientHom (Polynomials n) ideal

      generator : (i : Fin n) → ⟨ algebra ⟩ₐ
      generator = ⟨ π ⟩ₐ→ ∘ var

  isFP : (A : CommAlgebra R ℓ') → Type (ℓ-max ℓ ℓ')
  isFP A = ∃[ p ∈ FinitePresentation ] CommAlgebraEquiv (FinitePresentation.algebra p) A

  opaque
    isFPIsProp : {A : CommAlgebra R ℓ'} → isProp (isFP A)
    isFPIsProp = isPropPropTrunc
