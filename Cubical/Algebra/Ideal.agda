{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Ideal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic using ([_]; _∈_)

open import Cubical.Algebra.Ring

private
  variable
    ℓ : Level

module _ (R' : Ring {ℓ}) where

  open Ring R' renaming (Carrier to R)

  {- by default, 'ideal' means two-sided ideal -}
  record isIdeal (I : R → hProp ℓ) : Type ℓ where
    field
      +-closed : {x y : R} → x ∈ I → y ∈ I → (x + y) ∈ I
      -closed : {x : R} → x ∈ I → - x ∈ I
      0r-closed : 0r ∈ I
      ·-closedLeft : {x : R} → (r : R) → x ∈ I → r · x ∈ I
      ·-closedRight : {x : R} → (r : R) → x ∈ I → x · r ∈ I

  Ideal : Type _
  Ideal = Σ[ I ∈ (R → hProp ℓ) ] isIdeal I

  record isLeftIdeal (I : R → hProp ℓ) : Type ℓ where
    field
      +-closed : {x y : R} → x ∈ I → y ∈ I → (x + y) ∈ I
      -closed : {x : R} → x ∈ I → - x ∈ I
      0r-closed : 0r ∈ I
      ·-closedLeft : {x : R} → (r : R) → x ∈ I → r · x ∈ I


  record isRightIdeal (I : R → hProp ℓ) : Type ℓ where
    field
      +-closed : {x y : R} → x ∈ I → y ∈ I → (x + y) ∈ I
      -closed : {x : R} → x ∈ I → - x ∈ I
      0r-closed : 0r ∈ I
      ·-closedRight : {x : R} → (r : R) → x ∈ I → x · r ∈ I

  {- Examples of ideals -}
  zeroSubset : (x : R) → hProp ℓ
  zeroSubset x = (x ≡ 0r) , isSetRing R' _ _

  open Theory R'

  isIdealZeroIdeal : isIdeal zeroSubset
  isIdealZeroIdeal = record
                       { +-closed = λ x≡0 y≡0 → _ + _    ≡⟨ cong (λ u → u + _) x≡0 ⟩
                                                0r + _   ≡⟨ +-lid _ ⟩
                                                _        ≡⟨ y≡0 ⟩
                                                0r        ∎
                       ; -closed = λ x≡0 → - _ ≡⟨ cong (λ u → - u) x≡0 ⟩
                                           - 0r ≡⟨ 0-selfinverse ⟩
                                           0r ∎
                       ; 0r-closed = refl
                       ; ·-closedLeft = λ r x≡0 → r · _ ≡⟨ cong (λ u → r · u) x≡0 ⟩
                                                  r · 0r ≡⟨ 0-rightNullifies r  ⟩
                                                  0r ∎
                       ; ·-closedRight = λ r x≡0 → _ · r ≡⟨ cong (λ u → u · r) x≡0 ⟩
                                                   0r · r ≡⟨ 0-leftNullifies r ⟩
                                                   0r ∎
                       }

  zeroIdeal : Ideal
  zeroIdeal = zeroSubset , isIdealZeroIdeal
