{-# OPTIONS --safe #-}
module Cubical.ZCohomology.Groups.CP2 where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Int
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Algebra.Group
  renaming (ℤ to ℤGroup) hiding (Unit)

open import Cubical.HITs.Pushout
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Hopf
open import Cubical.HITs.Join
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim2 to pElim2 ; ∣_∣ to ∣_∣₁)

open IsGroupHom
open Iso

CP² : Type
CP² = Pushout {A = TotalHopf} fst λ _ → tt

module M = MV (S₊ 2) Unit TotalHopf fst (λ _ → tt)

H²CP²≅ℤ : GroupIso (coHomGr 2 CP²) ℤGroup
H²CP²≅ℤ = compGroupIso (BijectionIso→GroupIso bij)
            (compGroupIso (invGroupIso trivIso) (Hⁿ-Sⁿ≅ℤ 1))
  where
  isContrH¹TotalHopf : isContr (coHom 1 TotalHopf)
  isContrH¹TotalHopf =
    isOfHLevelRetractFromIso 0 (setTruncIso (domIso (invIso (IsoS³TotalHopf))))
      (isOfHLevelRetractFromIso 0 ((fst (H¹-Sⁿ≅0 1))) isContrUnit)

  isContrH²TotalHopf : isContr (coHom 2 TotalHopf)
  isContrH²TotalHopf =
    isOfHLevelRetractFromIso 0 (setTruncIso (domIso (invIso (IsoS³TotalHopf))))
      ((isOfHLevelRetractFromIso 0
        (fst (Hⁿ-Sᵐ≅0 1 2 λ p → snotz (sym (cong predℕ p)))) isContrUnit))

  trivIso : GroupIso (coHomGr 2 (Susp S¹)) (×coHomGr 2 (Susp S¹) Unit)
  fun (fst trivIso) x = x , 0ₕ _
  inv (fst trivIso) = fst
  rightInv (fst trivIso) (x , p) =
    ΣPathP (refl , isContr→isProp (isContrHⁿ-Unit 1) _ _)
  leftInv (fst trivIso) x = refl
  snd trivIso = makeIsGroupHom λ _ _ → refl

  bij : BijectionIso (coHomGr 2 CP²) (×coHomGr 2 (Susp S¹) Unit)
  BijectionIso.fun bij = M.i 2
  BijectionIso.inj bij x p =
    pRec (squash₂ _ _)
      (uncurry (λ z q
        → sym q
        ∙∙ cong (fst (M.d 1)) (isContr→isProp isContrH¹TotalHopf z (0ₕ _))
        ∙∙ (M.d 1) .snd .pres1))
      (M.Ker-i⊂Im-d 1 x p)
    where
    help : isInIm (M.d 1) x
    help = M.Ker-i⊂Im-d 1 x p
  BijectionIso.surj bij y =
    M.Ker-Δ⊂Im-i 2 y (isContr→isProp isContrH²TotalHopf _ _)

H⁴CP²≅ℤ : GroupIso (coHomGr 4 CP²) ℤGroup
H⁴CP²≅ℤ = compGroupIso (invGroupIso (BijectionIso→GroupIso bij))
          (compGroupIso help (Hⁿ-Sⁿ≅ℤ 2))
  where
  help : GroupIso (coHomGr 3 TotalHopf) (coHomGr 3 (S₊ 3))
  help = isoType→isoCohom 3 (invIso IsoS³TotalHopf)

  bij : BijectionIso (coHomGr 3 TotalHopf) (coHomGr 4 CP²)
  BijectionIso.fun bij = M.d 3
  BijectionIso.inj bij x p =
    pRec (squash₂ _ _)
         (uncurry (λ z q →
             sym q
          ∙∙ cong (M.Δ 3 .fst)
                (isOfHLevelΣ 1 (isContr→isProp
                  (isOfHLevelRetractFromIso 0
                    (fst (Hⁿ-Sᵐ≅0 2 1 λ p → snotz (cong predℕ p))) isContrUnit))
                (λ _ → isContr→isProp (isContrHⁿ-Unit 2))
                z (0ₕ _ , 0ₕ _))
          ∙∙ M.Δ 3 .snd .pres1))
         (M.Ker-d⊂Im-Δ _ x p)
  BijectionIso.surj bij y =
    M.Ker-i⊂Im-d 3 y (isOfHLevelΣ 1
      (isContr→isProp (isOfHLevelRetractFromIso 0
        (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p))) isContrUnit))
        (λ _ → isContr→isProp (isContrHⁿ-Unit _)) _ _)


-- Another Brunerie number
ℤ→HⁿCP²→ℤ : ℤ → ℤ
ℤ→HⁿCP²→ℤ x =
  Iso.fun (fst H⁴CP²≅ℤ)
    (Iso.inv (fst H²CP²≅ℤ) x ⌣ Iso.inv (fst H²CP²≅ℤ) x)

brunerie2 : ℤ
brunerie2 = ℤ→HⁿCP²→ℤ 1

{-
|brunerie2|≡1 : abs (ℤ→HⁿCP²→ℤ 1) ≡ 1
|brunerie2|≡1 = refl
-}
