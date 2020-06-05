{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.FreeCommAlgebra where
{-
  The free commutative algebra over a commutative ring,
  or in other words the ring of polynomials with coefficients in a given ring.
  Note that this is a constructive definition, which entails that polynomials
  cannot be represented by lists of coefficients, where the last one is non-zero.
  For rings with decidable equality, that is still possible.

  I learned about this (and other) definition(s) from David Jaz Myers.
  You can watch him talk about these things here:
  https://www.youtube.com/watch?v=VNp-f_9MnVk
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Structures.CommRing
open import Cubical.Structures.Algebra

private
  variable
    ℓ ℓ′ : Level

module construction (R : CommRing {ℓ}) where
  open Cubical.Structures.Algebra.over (CommRing→Ring R)
  open commring-syntax R hiding (-_; ₀) renaming (_+_ to _+s_; _·_ to _·s_; ₁ to ₁s)

  data R[_] (I : Type ℓ′) : Type (ℓ-max ℓ ℓ′) where
    var : I → R[ I ]
    const : ⟨ R ⟩ → R[ I ]
    _+_ : R[ I ] → R[ I ] → R[ I ]
    -_ : R[ I ] → R[ I ]
    ₀ : R[ I ]                               -- \_0

    +-assoc : (x y z : R[ I ]) → x + (y + z) ≡ (x + y) + z
    +-rid : (x : R[ I ]) → x + ₀ ≡ x
    +-comm : (x y : R[ I ]) → x + y ≡ y + x
    +-rinv : (x : R[ I ]) → x + (- x) ≡ ₀

    _·_ : R[ I ] → R[ I ] → R[ I ]            -- \cdot
    ₁ : R[ I ]
    ·-assoc : (x y z : R[ I ]) → x · (y · z) ≡ (x · y) · z
    ·-lid : (x : R[ I ]) → ₁ · x ≡ x
    ·-comm : (x y : R[ I ]) → x · y ≡ y · x

    ldist : (x y z : R[ I ]) → (x + y) · z ≡ (x · z) + (y · z)

    _⋆_ : ⟨ R ⟩ → R[ I ] → R[ I ]        -- \*
    ⋆-assoc : (s t : ⟨ R ⟩) (x : R[ I ]) → s ⋆ (t ⋆ x) ≡ (s ·s t) ⋆ x
    ⋆-assoc-· : (s : ⟨ R ⟩) (x y : R[ I ]) → s ⋆ (x · y) ≡ (s ⋆ x) · y
    ⋆-ldist-+ : (s t : ⟨ R ⟩) (x : R[ I ]) → (s +s t) ⋆ x ≡ (s ⋆ x) + (t ⋆ x)
    ⋆-rdist-+ : (s : ⟨ R ⟩) (x y : R[ I ]) → s ⋆ (x + y) ≡ (s ⋆ x) + (s ⋆ y)
    1-acts-trivial : (x : R[ I ]) → ₁s ⋆ x ≡ x

    0-trunc : (x y : R[ I ]) (p q : x ≡ y) → p ≡ q
