{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.CommRing
open import Cubical.Structures.Ring hiding (⟨_⟩)

private
  variable
    ℓ : Level

module _ (R : CommRing {ℓ}) where

  rawAlgebraStructure : Type ℓ → Type ℓ
  rawAlgebraStructure A = (⟨ R ⟩ → A → A)
                          × raw-ring-structure A

  rawStrIsoScalarMultiplication : StrIso {ℓ} (λ A → (⟨ R ⟩ → A → A)) ℓ
  rawStrIsoScalarMultiplication (A , ⋆-A) (B , ⋆-B) f =
    (r : ⟨ R ⟩) → (x : A) → equivFun f (⋆-A r x) ≡ ⋆-B r ((equivFun f) x)

  scalarMultiplicationFunExt : {A : Type ℓ}
     → (s t : ⟨ R ⟩ → A → A)
     → ((r : ⟨ R ⟩) → (x : A) → s r x ≡ t r x) ≃ (s ≡ t)
  scalarMultiplicationFunExt s t =
    isoToEquiv (iso (λ φ i r x → φ r x i)
                    (λ ψ r x i → ψ i r x)
                    (λ _ → refl) λ _ → refl)

  rawStrIsoScalarMultiplication-SNS : SNS _ rawStrIsoScalarMultiplication
  rawStrIsoScalarMultiplication-SNS =
    SNS-≡→SNS-PathP rawStrIsoScalarMultiplication
                    scalarMultiplicationFunExt

  rawAlgebraIsSNS : SNS {ℓ} rawAlgebraStructure _
  rawAlgebraIsSNS = join-SNS rawStrIsoScalarMultiplication rawStrIsoScalarMultiplication-SNS
                             ring-StrIso raw-ring-is-SNS

