{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.CommRing.Quotient.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Functions.Surjection

open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Sigma using (Σ≡Prop)

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/ₛ_)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.Kernel
open import Cubical.Algebra.Ring
import Cubical.Algebra.Ring.Quotient as Ring

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (R : CommRing ℓ) (I : IdealsIn R) where
  open CommRingStr (snd R)
  R/I = ⟨ R ⟩ /ₛ (λ x y → x - y ∈ (fst I))

  quotientCommRingStr : CommRingStr R/I
  quotientCommRingStr = snd
    (Ring→CommRing
        ((CommRing→Ring R) Ring./ (CommIdeal→Ideal I))
        (elimProp2 (λ _ _ → squash/ _ _)
                   λ x y i → [ CommRingStr.·Comm (snd R) x y i ]))

_/_ : (R : CommRing ℓ) (I : IdealsIn R) → CommRing ℓ
fst (R / I) = R/I R I
snd (R / I) = quotientCommRingStr R I

[_]/ : {R : CommRing ℓ} {I : IdealsIn R} → (a : fst R) → fst (R / I)
[ a ]/ = SQ.[ a ]

module Coherence (R : CommRing ℓ) (I : IdealsIn R) where
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

    0r≡ : RingStr.0r (CommRing→Ring (R / I) .snd) ≡ RingStr.0r ((CommRing→Ring R Ring./ CommIdeal→Ideal I) .snd)
    0r≡ = refl

  ringStr : RingHom (CommRing→Ring (R / I))
                ((CommRing→Ring R) Ring./ (CommIdeal→Ideal I))

  fst ringStr x = x
  (snd ringStr) = isRingHomCoh

  ringStrInv : RingHom ((CommRing→Ring R) Ring./ (CommIdeal→Ideal I))
                   (CommRing→Ring (R / I))

  fst ringStrInv x = x
  (snd ringStrInv) = isRingHomCohInv


open RingHoms

module _ (R : CommRing ℓ) (I : IdealsIn R) where

  quotientHom : CommRingHom R (R / I)
  quotientHom =
    withOpaqueStr $
    RingHom→CommRingHom $
        Coherence.ringStrInv R I
     ∘r Ring.quotientHom (CommRing→Ring R) (CommIdeal→Ideal I)

  quotientHomSurjective : isSurjection (quotientHom .fst)
  quotientHomSurjective = Ring.quotientHomSurjective (CommRing→Ring R) (CommIdeal→Ideal I)

  quotientHomEpi : (S : hSet ℓ')
                   → (f g : ⟨ R / I ⟩ → ⟨ S ⟩)
                   → f ∘ quotientHom .fst ≡ g ∘ quotientHom .fst
                   → f ≡ g
  quotientHomEpi S f g p =
      (Ring.quotientHomEpi
         (CommRing→Ring R) (CommIdeal→Ideal I) S
         f g p)

module Quotient-FGideal-CommRing-Ring
  (R : CommRing ℓ)
  (S : Ring ℓ')
  (f : RingHom (CommRing→Ring R) S)
  {n : ℕ}
  (v : FinVec ⟨ R ⟩ n)
  (fnull : (k : Fin n) → f $r v k ≡ RingStr.0r (snd S))
  where

  open RingStr (snd S) using (0r; is-set)

  Iv = generatedIdeal R v

  zeroOnGeneratedIdeal : (x : ⟨ R ⟩) → x ∈ fst Iv → f $r x ≡ 0r
  zeroOnGeneratedIdeal x x∈FGIdeal =
    PT.elim
      (λ _ → is-set (f $r x) 0r)
      (λ {(α , isLC) → subst _ (sym isLC) (cancelLinearCombination R S f _ α v fnull)})
      x∈FGIdeal

  inducedHom : RingHom (CommRing→Ring (R / (generatedIdeal _ v))) S
  inducedHom = Ring.UniversalProperty.inducedHom
                 (CommRing→Ring R) (CommIdeal→Ideal Iv) f zeroOnGeneratedIdeal
               ∘r (Coherence.ringStr R Iv)

module Quotient-FGideal-CommRing-CommRing
  (R : CommRing ℓ)
  (S : CommRing ℓ')
  (f : CommRingHom R S)
  {n : ℕ}
  (v : FinVec ⟨ R ⟩ n)
  (fnull : (k : Fin n) → f $cr v k ≡ CommRingStr.0r (snd S))
  where

  inducedHom : CommRingHom (R / (generatedIdeal _ v)) S
  inducedHom = RingHom→CommRingHom $
               Quotient-FGideal-CommRing-Ring.inducedHom R (CommRing→Ring S) (CommRingHom→RingHom f) v fnull

module UniversalProperty
  (R S : CommRing ℓ)
  (I : IdealsIn R)
  (f : CommRingHom R S)
  (I⊆ker : (x : ⟨ R ⟩) → x ∈ fst I → fst f x ≡ CommRingStr.0r (snd S))
  where

  inducedHom : CommRingHom (R / I) S
  inducedHom =
    withOpaqueStr $
    RingHom→CommRingHom $
       Ring.UniversalProperty.inducedHom
         (CommRing→Ring R)
         (CommIdeal→Ideal I)
         (CommRingHom→RingHom f)
         I⊆ker
      ∘r Coherence.ringStr R I

  opaque
    isSolution : inducedHom ∘cr quotientHom R I ≡ f
    isSolution = Σ≡Prop (λ _ → isPropIsCommRingHom _ _ _)
                       (cong fst (Ring.UniversalProperty.solution
                                        (CommRing→Ring R)
                                        (CommIdeal→Ideal I)
                                        (CommRingHom→RingHom f)
                                        I⊆ker))

  opaque
    isUnique : (ψ : CommRingHom (R / I) S) → (ψIsSolution : ψ .fst ∘ quotientHom R I .fst ≡ f .fst)
             →  ψ ≡ inducedHom
    isUnique ψ ψIsSolution =
      Σ≡Prop (λ _ → isPropIsCommRingHom _ _ _)
             (cong fst
                   (Ring.UniversalProperty.unique'
                       (CommRing→Ring R)
                       (CommIdeal→Ideal I)
                       (CommRingHom→RingHom f)
                       I⊆ker
                       (CommRingHom→RingHom ψ)
                       ψIsSolution))


module _ {R : CommRing ℓ} (I : IdealsIn R) where
  open CommRingStr ⦃...⦄
  private
    π = quotientHom R I
    instance _ = snd R
             _ = snd (R / I)

  opaque
    kernel≡I : kernelIdeal R (R / I) π ≡ I
    kernel≡I =
      Σ≡Prop (CommIdeal.isPropIsCommIdeal _)
            (funExt
             λ x → Σ≡Prop (λ _ → isPropIsProp)
                     let reason = cong (λ y → π .fst x ≡ y) (Coherence.0r≡ R I)
                     in (π .fst x ≡ RingStr.0r (CommRing→Ring (R / I) .snd)                       ≡⟨ reason ⟩
                         π .fst x ≡ RingStr.0r ((CommRing→Ring R Ring./ CommIdeal→Ideal I) .snd) ∎))
     ∙ cong Ideal→CommIdeal (Ring.kernel≡I (CommIdeal→Ideal I))

  zeroOnIdeal : (x : ⟨ R ⟩) → x ∈ fst I → fst π x ≡ 0r
  zeroOnIdeal x x∈I = subst (λ P → fst ((fst P) x)) (sym kernel≡I) x∈I
