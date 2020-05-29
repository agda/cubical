{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.Ring
open import Cubical.Structures.AbGroup hiding (⟨_⟩)
open import Cubical.Structures.Group using (raw-group-structure)
open import Cubical.Structures.Module

private
  variable
    ℓ : Level

module _ (R : Ring {ℓ}) where
  open ring-syntax

  rawAlgebraStructure : Type ℓ → Type ℓ
  rawAlgebraStructure = (addLeftMultiplication R) raw-ring-structure

  rawAlgebraIsSNS : SNS {ℓ} rawAlgebraStructure _
  rawAlgebraIsSNS = join-SNS (rawStrIsoScalarMultiplication R) (rawStrIsoScalarMultiplication-SNS R)
                             ring-StrIso raw-ring-is-SNS

  algebraAxioms : (A : Type ℓ) (str : rawAlgebraStructure A) → Type ℓ
  algebraAxioms A (_⋆_ , (_+_ , ₁ , _·_)) =
               ring-axioms A (_+_ , ₁ , _·_)
               × moduleAxioms R A (_⋆_ , _+_)
               × ((r : ⟨ R ⟩) (x y : A) → (r ⋆ x) · y ≡ r ⋆ (x · y))
               × ((r : ⟨ R ⟩) (x y : A) → r ⋆ (x · y) ≡ x · (r ⋆ y))

  algebraStructure : Type ℓ → Type ℓ
  algebraStructure = add-to-structure rawAlgebraStructure algebraAxioms

  algebraStrIso : StrIso rawAlgebraStructure ℓ
  algebraStrIso = join-iso (rawStrIsoScalarMultiplication R) ring-StrIso

  algebraIso : StrIso algebraStructure ℓ
  algebraIso = add-to-iso algebraStrIso algebraAxioms

  algebraAxiomIsProp : (A : Type ℓ) (str : rawAlgebraStructure A)
                       → isProp (algebraAxioms A str)
  algebraAxiomIsProp A (_⋆_ , (_+_ , ₁ , _·_)) =
                                       isPropΣ (ring-axioms-isProp A ((_+_ , ₁ , _·_)))
    λ ((((isSet-A , _), _) , _) , _) → isPropΣ (moduleAxiomsIsProp R A (_⋆_ , _+_))
                                 λ _ → isPropΣ (isPropΠ3 (λ _ _ _ → isSet-A _ _) )
                                          λ _ → isPropΠ3 (λ _ _ _ → isSet-A _ _)

  algebraIsSNS : SNS {ℓ} algebraStructure algebraIso
  algebraIsSNS = add-axioms-SNS _ algebraAxiomIsProp rawAlgebraIsSNS


Algebra : (R : Ring {ℓ}) → Type (ℓ-suc ℓ)
Algebra {ℓ} R = TypeWithStr ℓ (algebraStructure R)

AlgebraPath : (R : Ring {ℓ}) → (A B : Algebra {ℓ} R)
              → (A ≃[ algebraIso R ] B) ≃ (A ≡ B)
AlgebraPath R = SIP (algebraIsSNS R)
