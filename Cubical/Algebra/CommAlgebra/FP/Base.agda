{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.FP.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
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
open import Cubical.Algebra.CommAlgebra.Instances.Polynomials
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommAlgebra.Kernel


private
  variable
    ℓ ℓ' : Level

module _ (R : CommRing ℓ) where
  Polynomials : (n : ℕ) → CommAlgebra R ℓ
  Polynomials n = R [ Fin n ]ₐ

  FPCAlgebra : {m : ℕ} (n : ℕ) (relations : FinVec ⟨ Polynomials n ⟩ₐ m) → CommAlgebra R ℓ
  FPCAlgebra n relations = Polynomials n / ⟨ relations ⟩[ Polynomials n ]

  record FinitePresentation (A : CommAlgebra R ℓ') : Type (ℓ-max ℓ ℓ') where
    no-eta-equality
    field
      n : ℕ
      m : ℕ
      relations : FinVec ⟨ Polynomials n ⟩ₐ m
      equiv : CommAlgebraEquiv (FPCAlgebra n relations) A

  abstract
    isFP : (A : CommAlgebra R ℓ') → Type (ℓ-max ℓ ℓ')
    isFP A = ∥ FinitePresentation A ∥₁

    isFPIsProp : {A : CommAlgebra R ℓ} → isProp (isFP A)
    isFPIsProp = isPropPropTrunc
