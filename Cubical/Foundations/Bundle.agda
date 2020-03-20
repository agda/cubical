{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Bundle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Structures.TypeEqvTo

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
