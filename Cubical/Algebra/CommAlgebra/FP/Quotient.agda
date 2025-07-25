{-# OPTIONS --lossy-unification #-}
{- Quotient of fp R-algebra by an fg ideal is fp -}
module Cubical.Algebra.CommAlgebra.FP.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence

open import Cubical.Data.FinData
open import Cubical.Data.FinData.FiniteChoice as Finite
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal using (presLinearCombination; linearCombination)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Quotient
open import Cubical.Algebra.CommAlgebra.Quotient.FGIdealSum
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommAlgebra.Notation
open import Cubical.Algebra.CommAlgebra.FP

private variable
  ℓ ℓ' : Level

-- note that A is restricted to have the same universe level as R
module _ {R : CommRing ℓ} (A : FPCAlg R ℓ)  where

  module _ {k : ℕ} (g : FinVec ⟨ fst A ⟩ₐ k) where

    quotIsFP : isFP R (fst A / ⟨ g ⟩[ fst A ])
    quotIsFP = PT.rec isPropPropTrunc
                      makeFP
                      (A .snd)
      where
        makeFP : FPsOf R (fst A) → isFP R (fst A / ⟨ g ⟩[ fst A ])
        makeFP fpA =
          isFPByEquiv R (PQ / ⟨ g'' ⟩[ PQ ]) (A .fst / generatedIdeal (fst A) g)
            (commAlgIdealEquivToQuotientEquiv PQ ⟨ g'' ⟩[ PQ ] (A .fst) ⟨ g ⟩[ A .fst ] PQ≅A ⟨g''⟩≡⟨g⟩) isFPQuot
          where
            module A = FinitePresentation (fst fpA)
            ψ : CommAlgebraHom A.fpAlg (fst A)
            ψ = CommAlgebraEquiv→CommAlgebraHom (snd fpA)
            ψ⁻¹ : CommAlgebraHom (fst A) A.fpAlg
            ψ⁻¹ = CommAlgebraEquiv→CommAlgebraHom (invCommAlgebraEquiv (snd fpA))
            ψ⁻¹g : FinVec ⟨ A.fpAlg ⟩ₐ k
            ψ⁻¹g = ⟨ ψ⁻¹ ⟩ₐ→ ∘ g
            opaque
              unfolding A.fpAlg A.fgIdeal
              mereLiftOfψ⁻¹g : ∥ ((i : Fin k) → Σ[ g' ∈ ⟨ Polynomials R A.n ⟩ₐ ] A.π $ca g' ≡ ψ⁻¹g i) ∥₁
              mereLiftOfψ⁻¹g =
                Finite.choice (λ i → Σ[ g' ∈ ⟨ Polynomials R A.n ⟩ₐ ] A.π $ca g' ≡ ψ⁻¹g i)
                              (λ i → quotientHomSurjective (Polynomials R A.n) A.fgIdeal (ψ⁻¹g i))

            PQ : CommAlgebra R ℓ
            PQ = Polynomials R A.n / ⟨ A.relations ⟩[ Polynomials R A.n ]
            opaque
              unfolding A.fpAlg A.fgIdeal
              PQ≅A : CommAlgebraEquiv PQ (A .fst)
              PQ≅A = fpA .snd
              A≅PQ : CommAlgebraEquiv (A .fst) PQ
              A≅PQ = invCommAlgebraEquiv (fpA .snd)

              g'' : FinVec ⟨ PQ ⟩ₐ k
              g'' = ψ⁻¹g
              ⟨PQ≅A⟩ₐ≃∘g''≡g : ⟨ PQ≅A ⟩ₐ≃ ∘ g'' ≡ g
              ⟨PQ≅A⟩ₐ≃∘g''≡g = funExt (λ x → secEq (fpA .snd .fst) (g x))
              ⟨A≅PQ⟩ₐ≃∘g≡g'' : ⟨ A≅PQ ⟩ₐ≃ ∘ g ≡ g''
              ⟨A≅PQ⟩ₐ≃∘g≡g'' = refl -- funExt (λ x → {!retEq (fpA .snd .fst)  !})

              ⟨g''⟩≡⟨g⟩ : (x : ⟨ PQ ⟩ₐ) → (fst ⟨ g'' ⟩[ PQ ] x) ≡ (fst ⟨ g ⟩[ A .fst ] (⟨ PQ≅A ⟩ₐ≃ x))
              ⟨g''⟩≡⟨g⟩ x =
                Σ≡Prop (λ _ → isPropIsProp)
                $ hPropExt (fst ⟨ g'' ⟩[ PQ ] x .snd) (fst ⟨ g ⟩[ A .fst ] (⟨ PQ≅A ⟩ₐ≃ x) .snd)
                -- "⇒":
                     (λ x∈⟨g''⟩ →
                       PT.rec
                          isPropPropTrunc
                          (λ (α , x≡αg'') →
                           let
                             step1 = presLinearCombination
                                      (CommAlgebra→CommRing PQ) (CommAlgebra→CommRing (A .fst))
                                      (CommAlgebraEquiv→CommRingHom PQ≅A) k α g''
                             step2 = cong (linCombA (⟨ PQ≅A ⟩ₐ≃ ∘ α)) ⟨PQ≅A⟩ₐ≃∘g''≡g
                           in ∣ ⟨ PQ≅A ⟩ₐ≃ ∘ α ,
                            ((⟨ PQ≅A ⟩ₐ≃ x)                                 ≡⟨ cong ⟨ PQ≅A ⟩ₐ≃ x≡αg'' ⟩
                             ⟨ PQ≅A ⟩ₐ≃ (linCombPQ α g'')                   ≡⟨ step1 ⟩
                             linCombA (⟨ PQ≅A ⟩ₐ≃ ∘ α) (⟨ PQ≅A ⟩ₐ≃ ∘ g'')   ≡⟨ step2 ⟩
                             linCombA (⟨ PQ≅A ⟩ₐ≃ ∘ α) g ∎) ∣₁)
                          x∈⟨g''⟩)
                -- "⇐":
                     (λ ψx∈⟨g⟩ →
                       PT.rec
                         isPropPropTrunc
                         (λ (α , ψx≡αg) →
                           let step1 =
                                 presLinearCombination
                                   (CommAlgebra→CommRing (A .fst)) (CommAlgebra→CommRing PQ)
                                   (CommAlgebraEquiv→CommRingHom A≅PQ) k α g
                           in ∣ ⟨ A≅PQ ⟩ₐ≃ ∘ α ,
                             (x                                           ≡⟨ (sym $ retEq (fpA .snd .fst) x) ⟩
                              ⟨ A≅PQ ⟩ₐ≃ (⟨ PQ≅A ⟩ₐ≃ x)                   ≡⟨ cong ⟨ A≅PQ ⟩ₐ≃ ψx≡αg ⟩
                              ⟨ A≅PQ ⟩ₐ≃ (linCombA α g)                   ≡⟨ step1 ⟩
                              linCombPQ (⟨ A≅PQ ⟩ₐ≃ ∘ α) (⟨ A≅PQ ⟩ₐ≃ ∘ g) ∎) ∣₁)
                         ψx∈⟨g⟩)
               where linCombPQ : {l : ℕ} → FinVec ⟨ PQ ⟩ₐ l → FinVec ⟨ PQ ⟩ₐ l → ⟨ PQ ⟩ₐ
                     linCombPQ = linearCombination (CommAlgebra→CommRing PQ)
                     linCombA : {l : ℕ} → FinVec ⟨ A .fst ⟩ₐ l → FinVec ⟨ A .fst ⟩ₐ l → ⟨ A .fst ⟩ₐ
                     linCombA = linearCombination (CommAlgebra→CommRing (A .fst))
                     -- useLemma = presLinearCombination

            isFPQuot : isFP R (PQ / ⟨ g'' ⟩[ PQ ])
            isFPQuot =
              PT.rec isPropPropTrunc
                     (λ liftOfψ⁻¹g → ∣ useLift liftOfψ⁻¹g ∣₁)
                     mereLiftOfψ⁻¹g
              where
                liftVec : ((i : Fin k) → Σ[ g' ∈ ⟨ Polynomials R A.n ⟩ₐ ] A.π $ca g' ≡ ψ⁻¹g i)
                        → FinVec ⟨ Polynomials R A.n ⟩ₐ k
                liftVec liftOfψ⁻¹g i = liftOfψ⁻¹g i .fst
                useLift : ((i : Fin k) → Σ[ g' ∈ ⟨ Polynomials R A.n ⟩ₐ ] A.π $ca g' ≡ ψ⁻¹g i)
                          → FPsOf R (PQ / ⟨ g'' ⟩[ PQ ])
                useLift liftOfψ⁻¹g =
                  fpQ ,
                  (compCommAlgebraEquiv Q.fpAlgAsQuotient
                   $ compCommAlgebraEquiv (ideal≡ToEquiv fgIdeal≡)
                   $ compCommAlgebraEquiv (fgIdealSumEquiv (Polynomials R Q.n) A.relations (liftVec liftOfψ⁻¹g))
                                          e1)
                  where
                    fpQ = record { n = A.n ; m = A.m ℕ.+ k ; relations = A.relations ++Fin liftVec liftOfψ⁻¹g }
                    module Q = FinitePresentation fpQ
                    opaque
                      unfolding Q.fgIdeal
                      fgIdeal≡ : Q.fgIdeal ≡ ⟨ A.relations ++Fin liftVec liftOfψ⁻¹g ⟩[ Polynomials R Q.n ]
                      fgIdeal≡ = refl

                    -- we have to explicitly redefine the canonical map to solve a unfolding-depency problem
                    p : CommAlgebraHom (Polynomials R A.n) PQ
                    p = quotientHom (Polynomials R A.n) (generatedIdeal (Polynomials R A.n) A.relations)
                    opaque
                      unfolding A.fpAlg A.fgIdeal A.π g''
                      e1 : CommAlgebraEquiv
                                  (PQ / ⟨ ⟨ p ⟩ₐ→  ∘ (liftVec liftOfψ⁻¹g) ⟩[ PQ ])
                                  (PQ / ⟨ g'' ⟩[ PQ ])
                      e1 = ideal≡ToEquiv (cong (generatedIdeal PQ) (funExt λ i → liftOfψ⁻¹g i .snd))
