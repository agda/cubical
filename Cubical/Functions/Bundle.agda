{-# OPTIONS --cubical --safe #-}
module Cubical.Functions.Bundle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Fibration

open import Cubical.Foundations.Structure
open import Cubical.Structures.TypeEqvTo

open import Cubical.Data.Sigma.Properties
open import Cubical.HITs.PropositionalTruncation

module _ {ℓb ℓf} {B : Type ℓb} {F : Type ℓf} {ℓ} where

{-
    A fiber bundle with base space B and fibers F is a map `p⁻¹ : B → TypeEqvTo F`
     taking points in the base space to their respective fibers.

    e.g. a double cover is a map `B → TypeEqvTo Bool`
-}

  Total : (p⁻¹ : B → TypeEqvTo ℓ F) → Type (ℓ-max ℓb ℓ)
  Total p⁻¹ = Σ[ x ∈ B ] p⁻¹ x .fst

  pr : (p⁻¹ : B → TypeEqvTo ℓ F) → Total p⁻¹ → B
  pr p⁻¹ = fst

  inc : (p⁻¹ : B → TypeEqvTo ℓ F) (x : B) → p⁻¹ x .fst → Total p⁻¹
  inc p⁻¹ x = (x ,_)

  fibPrEquiv : (p⁻¹ : B → TypeEqvTo ℓ F) (x : B) → fiber (pr p⁻¹) x ≃ p⁻¹ x .fst
  fibPrEquiv p⁻¹ x = fiberEquiv (λ x → typ (p⁻¹ x)) x

module _ {ℓb ℓf} (B : Type ℓb) (ℓ : Level) (F : Type ℓf) where
  private
    ℓ' = ℓ-max ℓb ℓ

{-
    Equivalently, a fiber bundle with base space B and fibers F is a type E and
     a map `p : E → B` with fibers merely equivalent to F.
-}

  bundleEquiv : (B → TypeEqvTo ℓ' F) ≃ (Σ[ E ∈ Type ℓ' ] Σ[ p ∈ (E → B) ] ∀ x → ∥ fiber p x ≃ F ∥)
  bundleEquiv = compEquiv (compEquiv PiΣ (pathToEquiv p)) Σ-assoc
    where e = fibrationEquiv B ℓ
          p :   (Σ[ p⁻¹ ∈ (B → Type ℓ') ]            ∀ x → ∥ p⁻¹ x ≃ F ∥)
              ≡ (Σ[ p ∈ (Σ[ E ∈ Type ℓ' ] (E → B)) ] ∀ x → ∥ fiber (snd p) x ≃ F ∥ )
          p i = Σ[ q ∈ ua e (~ i) ] ∀ x → ∥ ua-unglue e (~ i) q x ≃ F ∥
