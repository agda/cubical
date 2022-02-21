{-
  This file defines cohomology of a type with
  coefficients in a dependent spectrum over it.

  This coincides with ZCohomology when the coefficients
  are constantly the Eilenberg-MacLane spectrum for ℤ
-}
{-# OPTIONS --safe #-}
module Cubical.Cohomology.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Properties

open import Cubical.Algebra.Group.Base

open import Cubical.Data.Int.Base hiding (_·_)
open import Cubical.Data.HomotopyGroup.Base
open import Cubical.HITs.SetTruncation

open import Cubical.Homotopy.Spectrum
open import Cubical.Homotopy.Prespectrum
open import Cubical.Homotopy.Loopspace
open import Cubical.Structures.Successor

private
  variable
    ℓ : Level

open Spectrum

module _ (X : Type ℓ) (A : (x : X) → Spectrum ℓ) where

  CoHom : ℤ → Type ℓ
  CoHom i = ∥ ((x : X) → fst (space (A x) i)) ∥₂

  module abGroupStr (k : ℤ) where
    CoHomAsGroup : Group ℓ
    CoHomAsGroup = (π^ 2) (Πᵘ∙ X  (λ x → (space (A x) (2 + k))))

    open GroupStr (snd CoHomAsGroup)

    isComm :  (a b : fst CoHomAsGroup) → a · b ≡ b · a
    isComm = elim2 (λ _ _ → isSetPathImplicit)
                   λ a b → ∣ a ∙ b ∣₂ ≡⟨ cong ∣_∣₂ {!isComm∙!} ⟩
                           ∣ b ∙ a ∣₂ ∎

  
