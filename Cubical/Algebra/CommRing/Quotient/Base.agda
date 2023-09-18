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
R / I =
  fst asRing , commringstr _ _ _ _ _
                 (iscommring (RingStr.isRing (snd asRing))
                             (elimProp2 (λ _ _ → squash/ _ _)
                                        commEq))
   where
       asRing = (CommRing→Ring R) Ring./ (CommIdeal→Ideal I)
       _·/_ : fst asRing → fst asRing → fst asRing
       _·/_ = RingStr._·_ (snd asRing)
       commEq : (x y : fst R) → ([ x ] ·/ [ y ]) ≡ ([ y ] ·/ [ x ])
       commEq x y i = [ CommRingStr.·Comm (snd R) x y i ]

[_]/ : {R : CommRing ℓ} {I : IdealsIn R} → (a : fst R) → fst (R / I)
[ a ]/ = [ a ]



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
  inducedHom = Ring.UniversalProperty.inducedHom (CommRing→Ring A) (CommIdeal→Ideal ideal) g zeroOnGeneratedIdeal
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

module UniversalProperty
  (R S : CommRing ℓ)
  (I : IdealsIn R)
  (f : CommRingHom R S)
  (I⊆ker : (x : ⟨ R ⟩) → x ∈ fst I → fst f x ≡ CommRingStr.0r (snd S))
  where

  inducedHom : CommRingHom (R / I) S
  inducedHom = Ring.UniversalProperty.inducedHom (CommRing→Ring R) (CommIdeal→Ideal I) f I⊆ker


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
