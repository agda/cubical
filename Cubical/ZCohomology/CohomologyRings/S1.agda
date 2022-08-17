{-# OPTIONS --safe --experimental-lossy-unification #-}

-- This file could be proven using the file Sn
-- However the proofs are easier than in Sn
-- And so kept for pedagogic reasons

module Cubical.ZCohomology.CohomologyRings.S1 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_ ; snotz to nsnotz)
open import Cubical.Data.Int
open import Cubical.Data.Vec
open import Cubical.Data.FinData

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int renaming (ℤGroup to ℤG)
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.QuotientRing
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤCommRing to ℤCR)
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-notationZ

open import Cubical.HITs.Truncation
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/sq_)
open import Cubical.HITs.Sn

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.CohomologyRing
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.CohomologyRings.CupProductProperties

open Iso

module Equiv-S1-Properties where

-----------------------------------------------------------------------------
-- Definitions

  open IsGroupHom
  open gradedRingProperties

  open CommRingStr (snd ℤCR) using ()
    renaming
    ( 0r        to 0ℤ
    ; 1r        to 1ℤ
    ; _+_       to _+ℤ_
    ; -_        to -ℤ_
    ; _·_       to _·ℤ_
    ; +Assoc    to +ℤAssoc
    ; +IdL      to +ℤIdL
    ; +IdR      to +ℤIdR
    ; +Comm     to +ℤComm
    ; ·Assoc    to ·ℤAssoc
    ; ·IdL      to ·ℤIdL
    ; ·IdR      to ·ℤIdR
    ; ·DistR+   to ·ℤDistR+
    ; is-set    to isSetℤ     )

  open RingStr (snd (H*R (S₊ 1))) using ()
    renaming
    ( 0r        to 0H*
    ; 1r        to 1H*
    ; _+_       to _+H*_
    ; -_        to -H*_
    ; _·_       to _cup_
    ; +Assoc    to +H*Assoc
    ; +IdL      to +H*IdL
    ; +IdR      to +H*IdR
    ; +Comm     to +H*Comm
    ; ·Assoc    to ·H*Assoc
    ; ·IdL      to ·H*IdL
    ; ·IdR      to ·H*IdR
    ; ·DistR+   to ·H*DistR+
    ; is-set    to isSetH*     )

  open CommRingStr (snd ℤ[X]) using ()
    renaming
    ( 0r        to 0Pℤ
    ; 1r        to 1Pℤ
    ; _+_       to _+Pℤ_
    ; -_        to -Pℤ_
    ; _·_       to _·Pℤ_
    ; +Assoc    to +PℤAssoc
    ; +IdL      to +PℤIdL
    ; +IdR      to +PℤIdR
    ; +Comm     to +PℤComm
    ; ·Assoc    to ·PℤAssoc
    ; ·IdL      to ·PℤIdL
    ; ·IdR      to ·PℤIdR
    ; ·Comm     to ·PℤComm
    ; ·DistR+   to ·PℤDistR+
    ; is-set    to isSetPℤ     )

  open CommRingStr (snd ℤ[X]/X²) using ()
    renaming
    ( 0r        to 0PℤI
    ; 1r        to 1PℤI
    ; _+_       to _+PℤI_
    ; -_        to -PℤI_
    ; _·_       to _·PℤI_
    ; +Assoc    to +PℤIAssoc
    ; +IdL      to +PℤIIdL
    ; +IdR      to +PℤIIdR
    ; +Comm     to +PℤIComm
    ; ·Assoc    to ·PℤIAssoc
    ; ·IdL      to ·PℤIIdL
    ; ·IdR      to ·PℤIIdR
    ; ·DistR+   to ·PℤIDistR+
    ; is-set    to isSetPℤI     )


  e₀ = invGroupIso (Hᵐ-Sⁿ 0 1)
  ϕ₀ = fun (fst e₀)
  ϕ₀str = snd e₀
  ϕ₀⁻¹ = inv (fst e₀)
  ϕ₀⁻¹str = snd (invGroupIso e₀)
  ϕ₀-sect = rightInv (fst e₀)
  ϕ₀-retr = leftInv (fst e₀)

  e₁ = invGroupIso (Hᵐ-Sⁿ 1 1)
  ϕ₁ = fun (fst e₁)
  ϕ₁str = snd e₁
  ϕ₁⁻¹ = inv (fst e₁)
  ϕ₁⁻¹str = snd (invGroupIso e₁)
  ϕ₁-sect = rightInv (fst e₁)
  ϕ₁-retr = leftInv (fst e₁)

-----------------------------------------------------------------------------
-- Direct Sens on ℤ[x]

  ℤ[x]→H*-S¹ : ℤ[x] → H* (S₊ 1)
  ℤ[x]→H*-S¹ = DS-Rec-Set.f _ _ _ _ isSetH*
                  0H*
                  ϕ
                  _+H*_
                  +H*Assoc
                  +H*IdR
                  +H*Comm
                  base-neutral-eq
                  base-add-eq
               where
               ϕ : _
               ϕ (zero ∷ [])        a = base 0 (ϕ₀ a)
               ϕ (one ∷ [])         a = base 1 (ϕ₁ a)
               ϕ (suc (suc n) ∷ []) a = 0H*

               base-neutral-eq :  _
               base-neutral-eq (zero ∷ [])        = cong (base 0) (pres1 ϕ₀str) ∙ base-neutral _
               base-neutral-eq (one ∷ [])         = cong (base 1) (pres1 ϕ₁str) ∙ base-neutral _
               base-neutral-eq (suc (suc n) ∷ []) = refl

               base-add-eq : _
               base-add-eq (zero ∷ []) a b        = (base-add _ _ _) ∙ (cong (base 0) (sym (pres· ϕ₀str _ _)))
               base-add-eq (one ∷ []) a b         = (base-add _ _ _) ∙ (cong (base 1) (sym (pres· ϕ₁str _ _)))
               base-add-eq (suc (suc n) ∷ []) a b = +H*IdR _

-----------------------------------------------------------------------------
-- Morphism on ℤ[x]

  ℤ[x]→H*-S¹-pres1Pℤ : ℤ[x]→H*-S¹ (1Pℤ) ≡ 1H*
  ℤ[x]→H*-S¹-pres1Pℤ = refl

  ℤ[x]→H*-S¹-pres+ : (x y : ℤ[x]) → ℤ[x]→H*-S¹ (x +Pℤ y) ≡ ℤ[x]→H*-S¹ x +H* ℤ[x]→H*-S¹ y
  ℤ[x]→H*-S¹-pres+ x y = refl

  ϕ₀-gen : (n : ℕ) → (f : coHom n (S₊ 1)) → ϕ₀ (pos 1) ⌣ f ≡ f
  ϕ₀-gen n = ST.elim (λ _ → isProp→isSet (GroupStr.is-set (snd (coHomGr n (S₊ 1))) _ _))
               λ f → cong ∣_∣₂ (funExt (λ x → rUnitₖ n (f x)))

  open pres⌣

  -- Nice packaging of the proof
  pres·-base-case-int : (n : ℕ) → (a : ℤ) → (m : ℕ) → (b : ℤ) →
                ℤ[x]→H*-S¹ (base (n ∷ []) a ·Pℤ base (m ∷ []) b)
              ≡ ℤ[x]→H*-S¹ (base (n ∷ []) a) cup ℤ[x]→H*-S¹ (base (m ∷ []) b)
  pres·-base-case-int zero          a zero          b = cong (base 0) (ϕₙ⌣ϕₘ ϕ₀ ϕ₀str ϕ₀ ϕ₀str ϕ₀ ϕ₀str (ϕ₀-gen _ _) a b)
  pres·-base-case-int zero          a one           b = cong (base 1) (ϕₙ⌣ϕₘ ϕ₀ ϕ₀str ϕ₁ ϕ₁str ϕ₁ ϕ₁str (ϕ₀-gen _ _) a b)
  pres·-base-case-int zero          a (suc (suc m)) b = refl
  pres·-base-case-int one           a zero          b = cong ℤ[x]→H*-S¹ (·PℤComm (base (1 ∷ []) a) (base (zero ∷ []) b))
                                                         ∙ pres·-base-case-int 0 b 1 a
                                                         ∙ gradCommRing (S₊ 1) 0 1 (inv (fst (Hᵐ-Sⁿ 0 1)) b) (inv (fst (Hᵐ-Sⁿ 1 1)) a)
  pres·-base-case-int one           a one           b = sym (base-neutral 2) ∙
                                                         cong (base 2) (isOfHLevelRetractFromIso 1 (fst (Hⁿ-Sᵐ≅0 1 0 nsnotz)) isPropUnit _ _)
  pres·-base-case-int one           a (suc (suc m)) b = refl
  pres·-base-case-int (suc (suc n)) a m             b = refl


  pres·-base-case-vec : (v : Vec ℕ 1) → (a : ℤ) → (v' : Vec ℕ 1) → (b : ℤ) →
                ℤ[x]→H*-S¹ (base v a ·Pℤ base v' b)
              ≡ ℤ[x]→H*-S¹ (base v a) cup ℤ[x]→H*-S¹ (base v' b)
  pres·-base-case-vec (n ∷ []) a (m ∷ []) b = pres·-base-case-int n a m b

  -- proof of the morphism
  ℤ[x]→H*-S¹-pres· : (x y : ℤ[x]) → ℤ[x]→H*-S¹ (x ·Pℤ y) ≡ ℤ[x]→H*-S¹ x cup ℤ[x]→H*-S¹ y
  ℤ[x]→H*-S¹-pres· = DS-Ind-Prop.f _ _ _ _
                         (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
                         (λ y → refl)
                         base-case
                         λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
    where
    base-case : _
    base-case (n ∷ []) a = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
                           (sym (RingTheory.0RightAnnihilates (H*R (S₊ 1)) _))
                           (λ v' b → pres·-base-case-vec (n ∷ []) a v' b)
                           λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*DistR+ _ _ _)


-----------------------------------------------------------------------------
-- Function on ℤ[x]/x + morphism

  ℤ[x]→H*-S¹-cancelX : (k : Fin 1) → ℤ[x]→H*-S¹ (<X²> k) ≡ 0H*
  ℤ[x]→H*-S¹-cancelX zero = refl

  ℤ[X]→H*-S¹ : RingHom (CommRing→Ring ℤ[X]) (H*R (S₊ 1))
  fst ℤ[X]→H*-S¹ = ℤ[x]→H*-S¹
  snd ℤ[X]→H*-S¹ = makeIsRingHom ℤ[x]→H*-S¹-pres1Pℤ ℤ[x]→H*-S¹-pres+ ℤ[x]→H*-S¹-pres·

  ℤ[X]/X²→H*R-S¹ : RingHom (CommRing→Ring ℤ[X]/X²) (H*R (S₊ 1))
  ℤ[X]/X²→H*R-S¹ =
    Quotient-FGideal-CommRing-Ring.inducedHom ℤ[X] (H*R (S₊ 1)) ℤ[X]→H*-S¹ <X²> ℤ[x]→H*-S¹-cancelX

  ℤ[x]/x²→H*-S¹ : ℤ[x]/x² → H* (S₊ 1)
  ℤ[x]/x²→H*-S¹ = fst ℤ[X]/X²→H*R-S¹



-----------------------------------------------------------------------------
-- Converse Sens on ℤ[X] + ℤ[x]/x

  H*-S¹→ℤ[x] : H* (S₊ 1) → ℤ[x]
  H*-S¹→ℤ[x] = DS-Rec-Set.f _ _ _ _ isSetPℤ
                  0Pℤ
                  ϕ⁻¹
                  _+Pℤ_
                  +PℤAssoc
                  +PℤIdR
                  +PℤComm
                  base-neutral-eq
                  base-add-eq
               where
               ϕ⁻¹ : _
               ϕ⁻¹ zero a          = base (0 ∷ []) (ϕ₀⁻¹ a)
               ϕ⁻¹ one a           = base (1 ∷ []) (ϕ₁⁻¹ a)
               ϕ⁻¹ (suc (suc n)) a = 0Pℤ

               base-neutral-eq : _
               base-neutral-eq zero          = cong (base (0 ∷ [])) (pres1 ϕ₀⁻¹str) ∙ base-neutral _
               base-neutral-eq one           = cong (base (1 ∷ [])) (pres1 ϕ₁⁻¹str) ∙ base-neutral _
               base-neutral-eq (suc (suc n)) = refl

               base-add-eq : _
               base-add-eq zero a b        = (base-add _ _ _) ∙ (cong (base (0 ∷ [])) (sym (pres· ϕ₀⁻¹str _ _)))
               base-add-eq one a b         = (base-add _ _ _) ∙ (cong (base (1 ∷ [])) (sym (pres· ϕ₁⁻¹str _ _)))
               base-add-eq (suc (suc n)) a b = +PℤIdR _

  H*-S¹→ℤ[x]-pres+ : (x y : H* (S₊ 1)) → H*-S¹→ℤ[x] ( x +H* y) ≡ H*-S¹→ℤ[x] x +Pℤ H*-S¹→ℤ[x] y
  H*-S¹→ℤ[x]-pres+ x y = refl

  H*-S¹→ℤ[x]/x² : H* (S₊ 1) → ℤ[x]/x²
  H*-S¹→ℤ[x]/x² = [_] ∘ H*-S¹→ℤ[x]

  H*-S¹→ℤ[x]/x²-pres+ : (x y : H* (S₊ 1)) → H*-S¹→ℤ[x]/x² (x +H* y) ≡ (H*-S¹→ℤ[x]/x² x) +PℤI (H*-S¹→ℤ[x]/x² y)
  H*-S¹→ℤ[x]/x²-pres+ x y = refl



-----------------------------------------------------------------------------
-- Section

  e-sect : (x : H* (S₊ 1)) → ℤ[x]/x²→H*-S¹ (H*-S¹→ℤ[x]/x² x) ≡ x
  e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
           refl
           base-case
           λ {U V} ind-U ind-V → cong₂ _+H*_ ind-U ind-V
           where
           base-case : _
           base-case zero          a = cong (base 0) (ϕ₀-sect _)
           base-case one           a = cong (base 1) (ϕ₁-sect _)
           base-case (suc (suc n)) a = (sym (base-neutral (suc (suc n))))
                                       ∙ cong (base (suc (suc n)))
                                            (isOfHLevelRetractFromIso 1 (fst (Hⁿ-Sᵐ≅0 (suc n) 0 nsnotz)) isPropUnit _ _)


-----------------------------------------------------------------------------
-- Retraction

  e-retr : (x : ℤ[x]/x²) → H*-S¹→ℤ[x]/x² (ℤ[x]/x²→H*-S¹ x) ≡ x
  e-retr = SQ.elimProp (λ _ → isSetPℤI _ _)
           (DS-Ind-Prop.f _ _ _ _ (λ _ → isSetPℤI _ _)
           refl
           base-case
           λ {U V} ind-U ind-V → cong₂ _+PℤI_ ind-U ind-V)
           where
           base-case : _
           base-case (zero ∷ [])        a = cong [_] (cong (base (0 ∷ [])) (ϕ₀-retr _))
           base-case (one ∷ [])         a = cong [_] (cong (base (1 ∷ [])) (ϕ₁-retr _))
           base-case (suc (suc n) ∷ []) a = eq/ 0Pℤ (base (suc (suc n) ∷ []) a) ∣ ((λ x → base (n ∷ []) (-ℤ a)) , helper) ∣₁
             where
             helper : _
             helper = (+PℤIdL _) ∙ cong₂ base (cong (λ X → X ∷ []) (sym (+-comm n 2))) (sym (·ℤIdR _)) ∙ (sym (+PℤIdR _))


-----------------------------------------------------------------------------
-- Computation of the Cohomology Ring

module _ where

  open Equiv-S1-Properties

  S¹-CohomologyRing : RingEquiv (CommRing→Ring ℤ[X]/X²) (H*R (S₊ 1))
  fst S¹-CohomologyRing = isoToEquiv is
    where
    is : Iso ℤ[x]/x² (H* (S₊ 1))
    fun is = ℤ[x]/x²→H*-S¹
    inv is = H*-S¹→ℤ[x]/x²
    rightInv is = e-sect
    leftInv is = e-retr
  snd S¹-CohomologyRing = snd ℤ[X]/X²→H*R-S¹

  CohomologyRing-S¹ : RingEquiv (H*R (S₊ 1)) (CommRing→Ring ℤ[X]/X²)
  CohomologyRing-S¹ = RingEquivs.invRingEquiv S¹-CohomologyRing
