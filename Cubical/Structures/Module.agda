{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Module where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.Ring
open import Cubical.Structures.AbGroup hiding (⟨_⟩)
open import Cubical.Structures.Group using (raw-group-structure; group-iso; raw-group-is-SNS)

private
  variable
    ℓ : Level

addLeftMultiplication : Ring {ℓ} → (Type ℓ → Type ℓ) → Type ℓ → Type ℓ
addLeftMultiplication R S A = (⟨ R ⟩ → A → A)
                              × S A

module _ (R : Ring {ℓ}) where
  open ring-syntax

  rawModuleStructure : Type ℓ → Type ℓ
  rawModuleStructure = (addLeftMultiplication R) raw-group-structure


  rawStrIsoScalarMultiplication : StrIso {ℓ} (λ A → (⟨ R ⟩ → A → A)) ℓ
  rawStrIsoScalarMultiplication (A , ⋆-A) (B , ⋆-B) f =
    (r : ⟨ R ⟩) → (x : A) → equivFun f (⋆-A r x) ≡ ⋆-B r ((equivFun f) x)

  scalarMultiplicationFunExt : {A : Type ℓ}
     → (s t : ⟨ R ⟩ → A → A)
     → ((r : ⟨ R ⟩) → (x : A) → s r x ≡ t r x) ≃ (s ≡ t)
  scalarMultiplicationFunExt s t =
    isoToEquiv (iso (λ φ i r x → φ r x i)
                    (λ ψ r x i → ψ i r x)
                    (λ _ → refl) (λ _ → refl))

  rawStrIsoScalarMultiplication-SNS : SNS _ rawStrIsoScalarMultiplication
  rawStrIsoScalarMultiplication-SNS =
    SNS-≡→SNS-PathP rawStrIsoScalarMultiplication
                    scalarMultiplicationFunExt

  moduleAxioms : (M : Type ℓ) (str : rawModuleStructure M) → Type ℓ
  moduleAxioms M (_⋆_ , _+_) = abelian-group-axioms M _+_
                               × ((r s : ⟨ R ⟩) (x : M) → (r ·⟨ R ⟩ s) ⋆ x ≡ r ⋆ (s ⋆ x))
                               × ((r s : ⟨ R ⟩) (x : M) → (r +⟨ R ⟩ s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x))
                               × ((r : ⟨ R ⟩) (x y : M) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y))
                               × ((x : M) → ₁⟨ R ⟩ ⋆ x ≡ x)

  moduleAxiomsIsProp : (M : Type ℓ) (str : rawModuleStructure M)
                       → isProp (moduleAxioms M str)
  moduleAxiomsIsProp M (_⋆_ , _+_) = isPropΣ (abelian-group-axioms-isProp M _+_)
    λ (((isSet-M , _) , _) , _)  →   isPropΣ (isPropΠ3 (λ _ _ _ → isSet-M _ _))
                               λ _ → isPropΣ (isPropΠ3 (λ _ _ _ → isSet-M _ _))
                               λ _ → isPropΣ (isPropΠ3 (λ _ _ _ → isSet-M _ _))
                                        λ _ → isPropΠ (λ _ → isSet-M _ _)

  moduleStructure : Type ℓ → Type ℓ
  moduleStructure = add-to-structure rawModuleStructure moduleAxioms
