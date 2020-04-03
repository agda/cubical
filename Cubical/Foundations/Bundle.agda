{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Bundle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
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

  module FibPrIso (p⁻¹ : B → TypeEqvTo ℓ F) (x : B) where

    fwd : fiber (pr p⁻¹) x → typ (p⁻¹ x)
    fwd ((x' , y) , p) = subst (λ z → typ (p⁻¹ z)) p y

    bwd : typ (p⁻¹ x) → fiber (pr p⁻¹) x
    bwd y = (x , y) , refl

    fwd-bwd : ∀ x → fwd (bwd x) ≡ x
    fwd-bwd y = transportRefl y

    bwd-fwd : ∀ x → bwd (fwd x) ≡ x
    bwd-fwd ((x' , y) , p) i = h (q i)
      where h : Σ[ s ∈ singl x ] typ (p⁻¹ (s .fst)) → fiber (pr p⁻¹) x
            h ((x , p) , y) = (x , y) , sym p
            q : Path (Σ[ s ∈ singl x ] typ (p⁻¹ (s .fst)))
                     ((x  , refl ) , subst (λ z → typ (p⁻¹ z)) p y)
                     ((x' , sym p) , y                            )
            q i = (contrSingl (sym p) i) , toPathP {A = λ i → typ (p⁻¹ (p (~ i)))}
                                           (transport⁻Transport (λ i → typ (p⁻¹ (p i))) y) i

    isom : Iso (fiber (pr p⁻¹) x) (typ (p⁻¹ x))
    isom = iso fwd bwd fwd-bwd bwd-fwd

  fibPrEquiv : (p⁻¹ : B → TypeEqvTo ℓ F) (x : B) → fiber (pr p⁻¹) x ≃ p⁻¹ x .fst
  fibPrEquiv p⁻¹ x = isoToEquiv (FibPrIso.isom p⁻¹ x)
