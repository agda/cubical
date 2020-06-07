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

module over (R : Ring {ℓ}) where
  open ring-syntax

  raw-algebra-structure : Type ℓ → Type ℓ
  raw-algebra-structure = (add-left-multiplication R) raw-ring-structure

  rawAlgebraIsSNS : SNS {ℓ} raw-algebra-structure _
  rawAlgebraIsSNS = join-SNS (rawStrIsoScalarMultiplication R) (rawStrIsoScalarMultiplication-SNS R)
                             ring-StrIso raw-ring-is-SNS

  algebra-axioms : (A : Type ℓ) (str : raw-algebra-structure A) → Type ℓ
  algebra-axioms A (_⋆_ , (_+_ , ₁ , _·_)) =
               ring-axioms A (_+_ , ₁ , _·_)
               × moduleAxioms R A (_⋆_ , _+_)
               × ((r : ⟨ R ⟩) (x y : A) → (r ⋆ x) · y ≡ r ⋆ (x · y))
               × ((r : ⟨ R ⟩) (x y : A) → r ⋆ (x · y) ≡ x · (r ⋆ y))

  algebraStructure : Type ℓ → Type ℓ
  algebraStructure = add-to-structure raw-algebra-structure algebra-axioms

  algebra-str-iso : StrIso raw-algebra-structure ℓ
  algebra-str-iso = join-iso (rawStrIsoScalarMultiplication R) ring-StrIso

  algebra-iso : StrIso algebraStructure ℓ
  algebra-iso = add-to-iso algebra-str-iso algebra-axioms

  algebraAxiomIsProp : (A : Type ℓ) (str : raw-algebra-structure A)
                       → isProp (algebra-axioms A str)
  algebraAxiomIsProp A (_⋆_ , (_+_ , ₁ , _·_)) =
                                       isPropΣ (ring-axioms-isProp A ((_+_ , ₁ , _·_)))
    λ ((((isSet-A , _), _) , _) , _) → isPropΣ (moduleAxiomsIsProp R A (_⋆_ , _+_))
                                 λ _ → isPropΣ (isPropΠ3 (λ _ _ _ → isSet-A _ _) )
                                          λ _ → isPropΠ3 (λ _ _ _ → isSet-A _ _)

  algebraIsSNS : SNS {ℓ} algebraStructure algebra-iso
  algebraIsSNS = add-axioms-SNS _ algebraAxiomIsProp rawAlgebraIsSNS

open over
Algebra : (R : Ring {ℓ}) → Type (ℓ-suc ℓ)
Algebra {ℓ} R = TypeWithStr ℓ (algebraStructure R)

AlgebraPath : (R : Ring {ℓ}) → (A B : Algebra {ℓ} R)
              → (A ≃[ algebra-iso R ] B) ≃ (A ≡ B)
AlgebraPath R = SIP (algebraIsSNS R)
