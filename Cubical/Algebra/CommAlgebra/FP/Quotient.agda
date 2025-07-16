{-# OPTIONS --safe #-}
{- Quotient of fp R-algebra by an fg ideal is fp -}
module Cubical.Algebra.CommAlgebra.FP.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.FinData.FiniteChoice
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommAlgebra.Notation
open import Cubical.Algebra.CommAlgebra.FP

private variable
  ℓ ℓ' : Level

module _ {R : CommRing ℓ} (A : FPCAlg R ℓ')  where

  module _ {k : ℕ} (G : FinVec ⟨ fst A ⟩ₐ k) where

    quotIsFP : isFP R (fst A / ⟨ G ⟩[ fst A ])
    quotIsFP = PT.rec isPropPropTrunc
                      makeFP
                      {!!}
      where
        makeFP : FPsOf R (fst A) → isFP R (fst A / ⟨ G ⟩[ fst A ])
        makeFP fpA = {!!}
          where open FinitePresentation (fst fpA)
                ψ : CommAlgebraHom fpAlg (fst A)
                ψ = CommAlgebraEquiv→CommAlgebraHom (snd fpA)
                ψ⁻¹ : CommAlgebraHom (fst A) fpAlg
                ψ⁻¹ = CommAlgebraEquiv→CommAlgebraHom (invCommAlgebraEquiv (snd fpA))
                ψ⁻¹G : FinVec ⟨ fpAlg ⟩ₐ k
                ψ⁻¹G = ⟨ ψ⁻¹ ⟩ₐ→ ∘ G
                opaque
                  unfolding fpAlg fgIdeal
                  liftOfψ⁻¹G : ∥ ((i : Fin k) → Σ[ G' ∈ ⟨ Polynomials R n ⟩ₐ ] π $ca G' ≡ ψ⁻¹G i) ∥₁
                  liftOfψ⁻¹G = choice (λ i → Σ[ G' ∈ ⟨ Polynomials R n ⟩ₐ ] π $ca G' ≡ ψ⁻¹G i)
                                      (λ i → quotientHomSurjective (Polynomials R n) fgIdeal (ψ⁻¹G i))

                  B : CommAlgebra R ℓ
                  B = Polynomials R n / ⟨ relations ⟩[ Polynomials R n ]
                  G'' : FinVec ⟨ B ⟩ₐ k
                  G'' = ψ⁻¹G
                  isFPQuot : isFP R (B / ⟨ G'' ⟩[ B ])
                  isFPQuot = {!!}
