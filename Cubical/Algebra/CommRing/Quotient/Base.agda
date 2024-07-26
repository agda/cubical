{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.CommRing.Quotient.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Functions.Surjection

open import Cubical.Data.Nat
open import Cubical.Data.FinData

open import Cubical.HITs.SetQuotients using ([_]; squash/; elimProp2)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.Kernel
open import Cubical.Algebra.Ring
import Cubical.Algebra.Ring.Quotient as Ring

private
  variable
    ℓ ℓ' : Level

_/_ : (R : CommRing ℓ) → (I : IdealsIn R) → CommRing ℓ
R / I = Ring→CommRing
          ((CommRing→Ring R) Ring./ (CommIdeal→Ideal I))
          (elimProp2 (λ _ _ → squash/ _ _)
                     λ x y i → [ CommRingStr.·Comm (snd R) x y i ])

[_]/ : {R : CommRing ℓ} {I : IdealsIn R} → (a : fst R) → fst (R / I)
[ a ]/ = [ a ]


module _ (R : CommRing ℓ) (I : IdealsIn R) where
  private
    opaque
      isRingHomCoh : IsRingHom (snd (CommRing→Ring (R / I)))
                               (λ x → x)
                               (snd ((CommRing→Ring R) Ring./ (CommIdeal→Ideal I)))
      IsRingHom.pres0 isRingHomCoh = refl
      IsRingHom.pres1 isRingHomCoh = refl
      IsRingHom.pres+ isRingHomCoh = λ _ _ → refl
      IsRingHom.pres· isRingHomCoh = λ _ _ → refl
      IsRingHom.pres- isRingHomCoh = λ _ → refl
      isRingHomCohInv : IsRingHom (snd ((CommRing→Ring R) Ring./ (CommIdeal→Ideal I)))
                               (λ x → x)
                               (snd (CommRing→Ring (R / I)))
      IsRingHom.pres0 isRingHomCohInv = refl
      IsRingHom.pres1 isRingHomCohInv = refl
      IsRingHom.pres+ isRingHomCohInv = λ _ _ → refl
      IsRingHom.pres· isRingHomCohInv = λ _ _ → refl
      IsRingHom.pres- isRingHomCohInv = λ _ → refl

  coh : RingHom (CommRing→Ring (R / I))
                ((CommRing→Ring R) Ring./ (CommIdeal→Ideal I))

  fst coh x = x
  (snd coh) = isRingHomCoh

  cohInv : RingHom ((CommRing→Ring R) Ring./ (CommIdeal→Ideal I))
                   (CommRing→Ring (R / I))

  fst cohInv x = x
  (snd cohInv) = isRingHomCohInv

open RingHoms
module Quotient-FGideal-CommRing-Ring
  (A : CommRing ℓ)
  (B : Ring ℓ')
  (g : RingHom (CommRing→Ring A) B)
  {n : ℕ}
  (v : FinVec ⟨ A ⟩ n)
  (gnull : (k : Fin n) → g $r v k ≡ RingStr.0r (snd B))
  where

  open RingStr (snd B) using (0r; is-set)

  zeroOnGeneratedIdeal : (x : ⟨ A ⟩) → x ∈ fst (generatedIdeal A v) → g $r x ≡ 0r
  zeroOnGeneratedIdeal x x∈FGIdeal =
    PT.elim
      (λ _ → is-set (g $r x) 0r)
      (λ {(α , isLC) → subst _ (sym isLC) (cancelLinearCombination A B g _ α v gnull)})
      x∈FGIdeal

  inducedHom : RingHom (CommRing→Ring (A / (generatedIdeal _ v))) B
  inducedHom = (Ring.UniversalProperty.inducedHom (CommRing→Ring A) (CommIdeal→Ideal ideal) g zeroOnGeneratedIdeal)
               ∘r coh A (generatedIdeal _ v)
    where ideal = generatedIdeal A v

module Quotient-FGideal-CommRing-CommRing
  (A : CommRing ℓ)
  (B : CommRing ℓ')
  (g : CommRingHom A B)
  {n : ℕ}
  (v : FinVec ⟨ A ⟩ n)
  (gnull : (k : Fin n) → g $r v k ≡ CommRingStr.0r (snd B))
  where

  inducedHom : CommRingHom (A / (generatedIdeal _ v)) B
  inducedHom = Quotient-FGideal-CommRing-Ring.inducedHom A (CommRing→Ring B) g v gnull
               ∘r cohInv _ _

module UniversalProperty
  (R S : CommRing ℓ)
  (I : IdealsIn R)
  (f : CommRingHom R S)
  (I⊆ker : (x : ⟨ R ⟩) → x ∈ fst I → fst f x ≡ CommRingStr.0r (snd S))
  where

  inducedHom : CommRingHom (R / I) S
  inducedHom = Ring.UniversalProperty.inducedHom (CommRing→Ring R) (CommIdeal→Ideal I) f I⊆ker
               ∘r coh _ _


quotientHom : (R : CommRing ℓ) → (I : IdealsIn R) → CommRingHom R (R / I)
quotientHom R I = Ring.quotientHom (CommRing→Ring R) (CommIdeal→Ideal I)

quotientHomSurjective : (R : CommRing ℓ) → (I : IdealsIn R)
                        → isSurjection (fst (quotientHom R I))
quotientHomSurjective R I = Ring.quotientHomSurjective (CommRing→Ring R) (CommIdeal→Ideal I)

module _ {R : CommRing ℓ} (I : IdealsIn R) where
  open CommRingStr ⦃...⦄
  private
    π = quotientHom R I
    instance _ = snd R
             _ = snd (R / I)

  kernel≡I : kernelIdeal R (R / I) π ≡ I
  kernel≡I = cong Ideal→CommIdeal (Ring.kernel≡I (CommIdeal→Ideal I))

  zeroOnIdeal : (x : ⟨ R ⟩) → x ∈ fst I → fst π x ≡ 0r
  zeroOnIdeal x x∈I = subst (λ P → fst ((fst P) x)) (sym kernel≡I) x∈I
