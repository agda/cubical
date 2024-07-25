{-# OPTIONS --safe #-}

module Cubical.Algebra.CommAlgebra.FreeCommAlgebra.UPAsCRing where
{-
  This file contains
  * The universal property of the free commutative algebra/polynomial ring
    as a commutative ring.

       R ──→ R[I]
        \     ∣
         f    ∃!          for a given φ : I → S
          ↘  ↙
            S

  The constructions use the universal property of the free commutative algebra
  from FreeCommAlgebra.Properties.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Function hiding (const)
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.HITs.SetTruncation

open import Cubical.Algebra.Ring
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

open RingHoms

module UniversalPropertyAsCommRing
         {R : CommRing ℓ} (I : Type ℓ')
         (S : CommRing ℓ'') (f : CommRingHom R S)
         (φ : I → ⟨ S ⟩)
         where

  private
    Sₐ : CommAlgebra R _
    Sₐ = CommAlgChar.toCommAlg R (S , f)

    cohSMap : CommRingHom (CommAlgebra→CommRing Sₐ) S
    cohSMap = CommRingEquiv→CommRingHom
                {A = CommAlgebra→CommRing Sₐ} {B = S}
                (CommAlgChar.CommAlgebra→CommRingEquiv R (S , f))

  inducedRingHom : CommRingHom (R [ I ]ᵣ) S
  inducedRingHom = cohSMap ∘r t
     where t : CommRingHom (R [ I ]ᵣ) (CommAlgebra→CommRing Sₐ)
           t = CommAlgebraHom→CommRingHom
                    (R [ I ]) Sₐ
                    (Theory.inducedHom Sₐ φ)

  private
    cohS : CommAlgChar.fromCommAlg R Sₐ .fst ≡ S
    cohS = cong fst (CommAlgChar.CommRingWithHomRoundTrip R (S , f))

    cohf : (CommAlgChar.fromCommAlg R Sₐ) .snd .fst ≡ f .fst
    cohf = cong (fst ∘ snd) (CommAlgChar.CommRingWithHomRoundTrip R (S , f))

    open CommAlgebraStr ((R [ I ]) .snd)
    cohConst : CommAlgChar.fromCommAlg R (R [ I ]) .snd .fst ≡ const
    cohConst = funExt (λ x → x ⋆ 1a ≡⟨ const⋆1a _ _ _ ⟩ const x ∎)

    cohSMapId : fst cohSMap ≡ idfun _
    cohSMapId = cong fst (CommAlgChar.CommAlgebra→CommRingIdEquiv R (S , f))

    cohInducedHom : fst (Theory.inducedHom Sₐ φ) ≡ fst inducedRingHom
    cohInducedHom =
      fst (Theory.inducedHom Sₐ φ)               ≡⟨ cong (_∘ fst (Theory.inducedHom Sₐ φ))
                                                        (sym cohSMapId) ⟩
      fst cohSMap ∘ fst (Theory.inducedHom Sₐ φ) ≡⟨⟩
      fst inducedRingHom ∎

  opaque
    inducedRingHomVar : fst inducedRingHom ∘ var ≡ φ
    inducedRingHomVar =
      fst inducedRingHom ∘ var                      ≡⟨ step1 ⟩
      (idfun _) ∘ fst (Theory.inducedHom Sₐ φ) ∘ var ≡⟨⟩
      fst (Theory.inducedHom Sₐ φ) ∘ var             ≡⟨ inducedHomOnVar Sₐ φ ⟩
      φ ∎
      where
        step1 : fst inducedRingHom ∘ var ≡ (idfun _) ∘ fst (Theory.inducedHom Sₐ φ) ∘ var
        step1 = cong (_∘ fst (Theory.inducedHom Sₐ φ) ∘ var) cohSMapId

  inducedRingHomCommutes : inducedRingHom ∘r (constHom R I) ≡ f
  inducedRingHomCommutes = Σ≡Prop (λ _ → isPropIsRingHom _ _ _) $
      fst (inducedRingHom ∘r (constHom R I))                                        ≡⟨⟩
      fst inducedRingHom ∘ fst (constHom R I)                                       ≡⟨ step1 ⟩
      fst (Theory.inducedHom Sₐ φ) ∘ fst (constHom R I)                             ≡⟨ step2 ⟩
      fst (Theory.inducedHom Sₐ φ) ∘ fst (CommAlgChar.fromCommAlg R (R [ I ]) .snd) ≡⟨ step3 ⟩
      fst f ∎
    where
      step1 = cong (_∘ fst (constHom R I)) (sym cohInducedHom)
      step2 = cong (fst (Theory.inducedHom Sₐ φ) ∘_) (sym cohConst)
      step3 = cong fst (snd (CommAlgChar.fromCommAlgebraHom R (R [ I ]) Sₐ (Theory.inducedHom Sₐ φ)))
              ∙ cohf

  private
    cohCAlgR[I] : CommAlgebraHom (R [ I ]) (CommAlgChar.toCommAlg R ((R [ I ]ᵣ) , constHom R I))
    cohCAlgR[I] = {!!}

  inducedRingHomUnique : (h : CommRingHom (R [ I ]ᵣ) S)
    → fst h ∘ var ≡ φ
    → h ∘r (constHom R I) ≡ f
    → h ≡ inducedRingHom
  inducedRingHomUnique h h∘var≡φ h∘const≡f = Σ≡Prop (λ _ → isPropIsRingHom _ _ _) $
    cong fst (inducedHomUnique Sₐ φ hₐ λ v →
      evaluateAt Sₐ hₐ v   ≡⟨ {!!} ⟩
      (fst h ∘ var) v     ≡[ i ]⟨ h∘var≡φ i v ⟩
      φ v ∎)
      ∙ cohInducedHom
    where open AlgebraHoms
          hₐ : CommAlgebraHom (R [ I ]) Sₐ
          hₐ = CommAlgChar.toCommAlgebraHom R (R [ I ]ᵣ , constHom R I) (S , f) h h∘const≡f ∘a cohCAlgR[I]
