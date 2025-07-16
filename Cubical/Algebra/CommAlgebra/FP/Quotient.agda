{-# OPTIONS --safe #-}
{- Quotient of fp R-algebra by an fg ideal is fp -}
module Cubical.Algebra.CommAlgebra.FP.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommAlgebra.FP

private variable
  ℓ : Level

module _ {R : CommRing ℓ} {k : ℕ} (A : CommAlgebra R ℓ) (fpA : FPsOf R A) (G : FinVec ⟨ A ⟩ₐ k)  where
  open FinitePresentation (fst fpA)
  ψ⁻¹ : CommAlgebraHom (A) fpAlg
  ψ⁻¹ = CommAlgebraEquiv→CommAlgebraHom (invCommAlgebraEquiv (snd fpA))
  ψ⁻¹G : FinVec ⟨ fpAlg ⟩ₐ k
  ψ⁻¹G = ⟨ ψ⁻¹ ⟩ₐ→ ∘ G
  opaque
    unfolding fpAlg fgIdeal

    B : CommAlgebra R ℓ
    B = Polynomials R n / ⟨ relations ⟩[ Polynomials R n ]
    G'' : FinVec ⟨ B ⟩ₐ k
    G'' = ψ⁻¹G
    isFPQuot : ⊥ → isFP R (B / ⟨ G'' ⟩[ B ])
    isFPQuot = ⊥.rec
