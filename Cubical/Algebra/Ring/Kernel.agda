module Cubical.Algebra.Ring.Kernel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.Ideal

private
  variable
    ℓ : Level

module _ {R S : Ring ℓ} (f′ : RingHom R S) where
  open IsRingHom (f′ .snd)
  open RingStr ⦃...⦄
  open isIdeal
  open RingTheory
  private
    instance
      _ = R
      _ = S
      _ = snd R
      _ = snd S
    f = fst f′

  kernel : fst R → hProp ℓ
  kernel x = (f x ≡ 0r) , is-set _ _

  kernelIsIdeal : isIdeal R kernel
  +-closed kernelIsIdeal =
    λ fx≡0 fy≡0 → f (_ + _)  ≡⟨ pres+ _ _ ⟩
                  f _ + f _  ≡⟨ cong (λ u → u + f _) fx≡0 ⟩
                  0r + f _   ≡⟨ cong (λ u → 0r + u) fy≡0 ⟩
                  0r + 0r    ≡⟨ 0Idempotent S ⟩
                  0r ∎
  -closed kernelIsIdeal =
    λ fx≡0 → f (- _)  ≡⟨ pres- _ ⟩
             - f _    ≡⟨ cong -_ fx≡0 ⟩
             - 0r     ≡⟨ 0Selfinverse S ⟩
             0r       ∎
  0r-closed kernelIsIdeal = f 0r ≡⟨ pres0 ⟩ 0r ∎
  ·-closedLeft kernelIsIdeal = λ r fx≡0 →
    f (r · _)    ≡⟨ pres· _ _ ⟩
    f r · f (_)  ≡⟨ cong (λ u → f r · u) fx≡0 ⟩
    f r · 0r     ≡⟨ 0RightAnnihilates S _ ⟩
    0r ∎
  ·-closedRight kernelIsIdeal = λ r fx≡0 →
    f (_ · r)    ≡⟨ pres· _ _ ⟩
    f _ · f r     ≡⟨ cong (λ u → u · f r) fx≡0 ⟩
    0r · f r      ≡⟨ 0LeftAnnihilates S _ ⟩
    0r ∎

  kernelIdeal : IdealsIn R
  fst kernelIdeal = kernel
  snd kernelIdeal = kernelIsIdeal


  kernelFiber : (x y : ⟨ R ⟩) → f x ≡ f y → x - y ∈ kernel
  kernelFiber x y fx≡fy = f (x - y)     ≡⟨ pres+ x (- y) ⟩
                          f x + f (- y) ≡[ i ]⟨ fx≡fy i + pres- y i ⟩
                          f y - f y     ≡⟨ +InvR (f y) ⟩
                          0r ∎
