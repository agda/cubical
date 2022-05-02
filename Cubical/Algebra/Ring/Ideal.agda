{-# OPTIONS --safe #-}
module Cubical.Algebra.Ring.Ideal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.Properties


private
  variable
    ℓ : Level

module _ (R' : Ring ℓ) where

  open RingStr (snd R')
  private R = ⟨ R' ⟩

  {- by default, 'ideal' means two-sided ideal -}
  record isIdeal (I : ℙ R) : Type ℓ where
    field
      +-closed : {x y : R} → x ∈ I → y ∈ I → x + y ∈ I
      -closed : {x : R} → x ∈ I → - x ∈ I
      0r-closed : 0r ∈ I
      ·-closedLeft : {x : R} → (r : R) → x ∈ I → r · x ∈ I
      ·-closedRight : {x : R} → (r : R) → x ∈ I → x · r ∈ I

  Ideal : Type _
  Ideal = Σ[ I ∈ ℙ R ] isIdeal I

  record isLeftIdeal (I : ℙ R) : Type ℓ where
    field
      +-closed : {x y : R} → x ∈ I → y ∈ I → x + y ∈ I
      -closed : {x : R} → x ∈ I → - x ∈ I
      0r-closed : 0r ∈ I
      ·-closedLeft : {x : R} → (r : R) → x ∈ I → r · x ∈ I


  record isRightIdeal (I : ℙ R) : Type ℓ where
    field
      +-closed : {x y : R} → x ∈ I → y ∈ I → x + y ∈ I
      -closed : {x : R} → x ∈ I → - x ∈ I
      0r-closed : 0r ∈ I
      ·-closedRight : {x : R} → (r : R) → x ∈ I → x · r ∈ I

  {- Examples of ideals -}
  zeroSubset : ℙ R
  zeroSubset x = (x ≡ 0r) , isSetRing R' _ _

  open RingTheory R'
  open isIdeal

  isIdealZeroIdeal : isIdeal zeroSubset
  +-closed isIdealZeroIdeal x≡0 y≡0 =
    _ + _    ≡⟨ cong (λ u → u + _) x≡0 ⟩
    0r + _   ≡⟨ +Lid _ ⟩
    _        ≡⟨ y≡0 ⟩
    0r       ∎
  -closed isIdealZeroIdeal x≡0 =
    - _  ≡⟨ cong (λ u → - u) x≡0 ⟩
    - 0r ≡⟨ 0Selfinverse ⟩
    0r   ∎
  0r-closed isIdealZeroIdeal = refl
  ·-closedLeft isIdealZeroIdeal r x≡0 =
    r · _  ≡⟨ cong (λ u → r · u) x≡0 ⟩
    r · 0r ≡⟨ 0RightAnnihilates r  ⟩
    0r     ∎
  ·-closedRight isIdealZeroIdeal r x≡0 =
    _ · r  ≡⟨ cong (λ u → u · r) x≡0 ⟩
    0r · r ≡⟨ 0LeftAnnihilates r ⟩
    0r     ∎

  zeroIdeal : Ideal
  zeroIdeal = zeroSubset , isIdealZeroIdeal

IdealsIn : (R : Ring ℓ) → Type _
IdealsIn {ℓ} R = Σ[ I ∈ ℙ ⟨ R ⟩ ] isIdeal R I
