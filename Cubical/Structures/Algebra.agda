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

  moduleAxioms : (M : Type ℓ) (str : rawModuleStructure R M) → Type ℓ
  moduleAxioms M (_⋆_ , _+_) = abelian-group-axioms M _+_
                               × ((r s : ⟨ R ⟩) (x : M) → (r ·⟨ R ⟩ s) ⋆ x ≡ r ⋆ (s ⋆ x))
                               × ((r s : ⟨ R ⟩) (x : M) → (r +⟨ R ⟩ s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x))
                               × ((r : ⟨ R ⟩) (x y : M) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y))
                               × ((x : M) → ((₁⟨ R ⟩) ⋆ x) ≡ x)

  algebraAxioms : (A : Type ℓ) (str : rawAlgebraStructure A) → Type ℓ
  algebraAxioms A (_⋆_ , (_+_ , ₁ , _·_)) =
               ring-axioms A (_+_ , ₁ , _·_)
               × moduleAxioms A (_⋆_ , _+_)
               × ((r : ⟨ R ⟩) (x y : A) → (r ⋆ x) · y ≡ r ⋆ (x · y))
               × ((r : ⟨ R ⟩) (x y : A) → r ⋆ (x · y) ≡ x · (r ⋆ y))

  algebraStructure : Type ℓ → Type ℓ
  algebraStructure = add-to-structure rawAlgebraStructure algebraAxioms
