{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Ideal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic using ([_])
open import Cubical.Structures.Ring

private
  variable
    ℓ ℓ′ : Level

infix 5 _∈_
_∈_ : {X : Type ℓ } → (x : X) → (P : X → hProp ℓ′) → Type _
x ∈ P = [ P x ]

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

  Ideal : Type _
  Ideal = Σ[ I ∈ (R → hProp ℓ) ] isIdeal I

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

  {- Examples of ideals -}
  zeroSubset : (x : R) → hProp ℓ
  zeroSubset x = (x ≡ ₀) , ringIsSet R′ x ₀

  open ring-axioms R′
  open calculations R′

  isIdealZeroIdeal : isIdeal zeroSubset
  isIdealZeroIdeal = record
                       { +-closed = λ x≡0 y≡0 → _ + _    ≡⟨ cong (λ u → u + _) x≡0 ⟩
                                                ₀ + _    ≡⟨ ring+-lid _ ⟩
                                                _        ≡⟨ y≡0 ⟩
                                                ₀        ∎
                       ; -closed = λ x≡0 → - _ ≡⟨ cong (λ u → - u) x≡0 ⟩
                                           - ₀ ≡⟨ 0-selfinverse ⟩
                                           ₀ ∎
                       ; ₀-closed = refl
                       ; ·-closedLeft = λ r x≡0 → r · _ ≡⟨ cong (λ u → r · u) x≡0 ⟩
                                                  r · ₀ ≡⟨ 0-rightNullifies r  ⟩
                                                  ₀ ∎
                       ; ·-closedRight = λ r x≡0 → _ · r ≡⟨ cong (λ u → u · r) x≡0 ⟩
                                                   ₀ · r ≡⟨ 0-leftNullifies r ⟩
                                                   ₀ ∎
                       }

  zeroIdeal : Ideal
  zeroIdeal = zeroSubset , isIdealZeroIdeal
