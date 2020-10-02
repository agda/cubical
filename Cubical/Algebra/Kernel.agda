{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Kernel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic using ([_]; _∈_)

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ideal

private
  variable
    ℓ : Level

module _ {{R S : Ring {ℓ}}} (f′ : RingHom R S) where
  open RingHom f′
  open HomTheory f′
  open Ring ⦃...⦄
  open isIdeal
  open Theory

  kernel : ⟨ R ⟩ → hProp ℓ
  kernel x = (f x ≡ 0r) , isSetRing S _ _

  kernelIsIdeal : isIdeal R kernel
  +-closed kernelIsIdeal =
    λ fx≡0 fy≡0 → f (_ + _)  ≡⟨ isHom+ _ _ ⟩
                  f _ + f _  ≡⟨ cong (λ u → u + f _) fx≡0 ⟩
                  0r + f _   ≡⟨ cong (λ u → 0r + u) fy≡0 ⟩
                  0r + 0r    ≡⟨ 0-idempotent S ⟩
                  0r ∎
  -closed kernelIsIdeal =
    λ fx≡0 → f (- _)  ≡⟨ -commutesWithHom _ ⟩
             - f _    ≡⟨ cong -_ fx≡0 ⟩
             - 0r     ≡⟨ 0-selfinverse S ⟩
             0r       ∎
  0r-closed kernelIsIdeal = f 0r ≡⟨ homPres0 ⟩ 0r ∎
  ·-closedLeft kernelIsIdeal = λ r fx≡0 →
    f (r · _)    ≡⟨ isHom· _ _ ⟩
    f r · f (_)  ≡⟨ cong (λ u → f r · u) fx≡0 ⟩
    f r · 0r     ≡⟨ 0-rightNullifies S _ ⟩
    0r ∎
  ·-closedRight kernelIsIdeal = λ r fx≡0 →
    f (_ · r)    ≡⟨ isHom· _ _ ⟩
    f _ · f r     ≡⟨ cong (λ u → u · f r) fx≡0 ⟩
    0r · f r      ≡⟨ 0-leftNullifies S _ ⟩
    0r ∎
