{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Ideal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Structures.Ring


private
  variable
    ℓ : Level
    ℓ′ : Level
    ℓ″ : Level

_holds : ∀ {ℓ} → hProp ℓ → Type ℓ
(P , _) holds = P

infix 5 _∈_
_∈_ : {X : Type ℓ′ } → (x : X) → (P : X → hProp ℓ″) → Type _
x ∈ P = P(x) holds

module _ (R′ : Ring {ℓ}) where
  private
    R = ⟨ R′ ⟩


  open ring-·syntax R′

  {- by default, 'ideal' means two-sided ideal -}
  record isIdeal (I : R → hProp ℓ′) : Type (ℓ-max ℓ′ ℓ) where
    field
      +-closed : {x y : R} → x ∈ I → y ∈ I → (x + y) ∈ I
      -closed : {x : R} → x ∈ I → - x ∈ I
      ₀-closed : ₀ ∈ I
      ·-closedLeft : {x : R} → (r : R) → x ∈ I → r · x ∈ I
      ·-closedRight : {x : R} → (r : R) → x ∈ I → x · r ∈ I


  record isLeftIdeal (I : R → hProp ℓ′) : Type (ℓ-max ℓ′ ℓ) where
    field
      +-closed : {x y : R} → x ∈ I → y ∈ I → (x + y) ∈ I
      -closed : {x : R} → x ∈ I → - x ∈ I
      ₀-closed : ₀ ∈ I
      ·-closedLeft : {x : R} → (r : R) → x ∈ I → r · x ∈ I


  record isRightIdeal (I : R → hProp ℓ′) : Type (ℓ-max ℓ′ ℓ) where
    field
      +-closed : {x y : R} → x ∈ I → y ∈ I → (x + y) ∈ I
      -closed : {x : R} → x ∈ I → - x ∈ I
      ₀-closed : ₀ ∈ I
      ·-closedRight : {x : R} → (r : R) → x ∈ I → x · r ∈ I


