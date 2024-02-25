{-
  The goal of this module is to compute the quotient by a sum of ideals, i.e. show:

    R / (I + J) = (R / I) / J
-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.CommRing.Quotient.IdealSum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding using (isEmbedding; injEmbedding)

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma

import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Quotient
open import Cubical.Algebra.CommRing.Kernel
open import Cubical.Algebra.CommRing.Ideal.Base
open import Cubical.Algebra.CommRing.Ideal.Sum
open import Cubical.Algebra.CommRing.Ideal.SurjectiveImage

open import Cubical.Tactics.CommRingSolver

private variable ℓ : Level

module Construction {R : CommRing ℓ} (I J : IdealsIn R) where
  open CommIdeal ⦃...⦄
  open IdealSum R
  open Cubical.Algebra.Ring.Properties.RingHoms
  open CommRingStr ⦃...⦄
  open IsRingHom ⦃...⦄

  {-
    We show ψ is an isomorphism, by showing it is
    surjectiv and has a trivial kernel.

              R ──π₁─→ R/I
              |         |
              |         π₂
              ↓         ↓
            R/I+J ─ψ→ (R/I)/J

  -}

  π₁ = quotientHom R I

  π₁J : IdealsIn (R / I)
  π₁J = imageIdeal π₁ (quotientHomSurjective R I) J

  π₂ = quotientHom (R / I) π₁J

  π : CommRingHom R ((R / I) / π₁J)
  π = π₂ ∘r π₁

  π+ : CommRingHom R (R / (I +i J))
  π+ = quotientHom R (I +i J)

  private instance _ = snd R
                   _ = snd (R / I)
                   _ = snd ((R / I) / π₁J)
                   _ = snd (R / (I +i J))

  πI+J≡0 : (x : ⟨ R ⟩) → x ∈ (I +i J) → fst π x ≡ 0r
  πI+J≡0 x  =
    PT.rec (is-set _ _)
           λ ((a , b) , (a∈I , b∈J , x≡a+b))
             → let instance _ = snd π
                   πa≡0 : fst π a ≡ 0r
                   πa≡0 = fst π₂ (fst π₁ a) ≡⟨ cong (fst π₂) (zeroOnIdeal I a a∈I) ⟩
                          fst π₂ 0r         ≡⟨ pres0 ⦃ snd π₂ ⦄ ⟩
                          0r ∎
                   πb≡0 : fst π b ≡ 0r
                   πb≡0 = zeroOnIdeal π₁J (fst π₁ b) ∣ b , (b∈J , refl) ∣₁
               in fst π x           ≡⟨ cong (fst π) x≡a+b ⟩
                  fst π (a + b)     ≡⟨ pres+ a b ⟩
                  fst π a + fst π b ≡[ i ]⟨ πa≡0 i + πb≡0 i ⟩
                  0r + 0r           ≡⟨ +IdL _ ⟩
                  0r ∎

  π⁻¹0≡I+J : (x : ⟨ R ⟩) → fst π x ≡ 0r → x ∈ (I +i J)
  π⁻¹0≡I+J x πx≡0 = PT.rec isPropPropTrunc (λ (b , b∈J , π₁b≡π₁x) → step2 b b∈J π₁b≡π₁x) π₁x∈J
    where π₁x∈J : (fst π₁ x) ∈ π₁J
          π₁x∈J = subst (fst π₁ x ∈_) (kernel≡I π₁J) πx≡0

          step1 : ∀ b → fst π₁ b ≡ fst π₁ x → - (b - x) ∈ I
          step1 b π₁b≡π₁x =
            -Closed I (b - x)
              (subst (λ K → b - x ∈ K) (kernel≡I I)
                  (kernelFiber R (R / I) π₁ b x π₁b≡π₁x))

          step2 : ∀ b → b ∈ J → fst π₁ b ≡ fst π₁ x → x ∈ (I +i J)
          step2 b b∈J π₁b≡π₁x =
            ∣ (- (b - x) , b) , (step1 b π₁b≡π₁x) , (b∈J , (x ≡⟨ solve! R ⟩ (- (b - x) + b) ∎)) ∣₁

  ψ : CommRingHom (R / (I +i J)) ((R / I) / π₁J)
  ψ = UniversalProperty.inducedHom R ((R / I) / π₁J) (I +i J) π πI+J≡0

  kernel-0 : (x : ⟨ R / (I +i J) ⟩) → fst ψ x ≡ 0r → x ≡ 0r
  kernel-0 x ψx≡0 =
    PT.rec (is-set x 0r)
           (λ (x' , π+x'≡x) →
             let πx'≡0 : fst π x' ≡ 0r
                 πx'≡0 = fst π x'          ≡⟨⟩
                         fst ψ (fst π+ x') ≡⟨ cong (fst ψ) π+x'≡x ⟩
                         fst ψ x           ≡⟨ ψx≡0 ⟩
                         0r ∎
             in subst (_≡ 0r)
                      π+x'≡x
                      (subst (x' ∈_)
                             (sym (kernel≡I (I +i J)))
                             (π⁻¹0≡I+J x' πx'≡0)))
           (quotientHomSurjective R (I +i J) x)

  {- workaround for slow type checking, more specifically,
    ψ x was slow to normalise and normalisation was triggered
    on plugging 'ϕ-injective' into 'injEmbedding'.
  -}
  abstract
    ϕ : CommRingHom (R / (I +i J)) ((R / I) / π₁J)
    ϕ = ψ

    ϕ-injective : {x y : ⟨ R / (I +i J) ⟩}
                → fst ϕ x ≡ fst ϕ y → x ≡ y
    ϕ-injective =
      RingHomTheory.ker≡0→inj
                  {R = CommRing→Ring (R / (I +i J))}
                  {S = CommRing→Ring ((R / I) / π₁J)}
                  ψ
                  λ {x} → kernel-0 x

    ϕ≡ψ : ϕ ≡ ψ
    ϕ≡ψ = refl

  embedding : isEmbedding {A = ⟨ R / (I +i J) ⟩} {B = ⟨ (R / I) / π₁J ⟩} (fst ϕ)
  embedding =
    injEmbedding
          is-set
          ϕ-injective


  surjective : isSurjection (fst ψ)
  surjective =
    leftFactorSurjective
      (fst π+)
      (fst ψ)
      (snd (compSurjection (_ , quotientHomSurjective R I) (_ , quotientHomSurjective (R / I) π₁J)))

module _ {R : CommRing ℓ} (I J : IdealsIn R) where
  open Construction I J
  open IdealSum R

  quotientIdealSumEquiv : CommRingEquiv (R / (I +i J)) ((R / I) / π₁J)
  fst (fst quotientIdealSumEquiv) = fst ψ
  snd (fst quotientIdealSumEquiv) =
    fst (invEquiv isEquiv≃isEmbedding×isSurjection)
        ((subst (λ ξ → isEmbedding (fst ξ)) ϕ≡ψ embedding) ,
         surjective)
  snd quotientIdealSumEquiv = snd ψ
