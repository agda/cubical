{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.S1 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_ ; snotz to nsnotz)
open import Cubical.Data.Int
open import Cubical.Data.Sum
open import Cubical.Data.Vec
open import Cubical.Data.FinData

open import Cubical.Algebra.Group hiding (Unit ; ℤ; Bool ; _/_ )
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤ to ℤCR)
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.QuotientRing

open import Cubical.Algebra.Direct-Sum.Base
open import Cubical.Algebra.AbGroup.Instances.Direct-Sum
open import Cubical.Algebra.Polynomials.Multivariate.Base renaming (base to baseP)
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly

open import Cubical.HITs.Truncation
open import Cubical.HITs.SetQuotients renaming (elimProp to elimProp-sq ; rec to rec-sq ; _/_ to _/sq_)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.CohomologyRing
open import Cubical.ZCohomology.CohomologyRings.Eliminator-Poly-Quotient-to-Ring

open import Cubical.Data.Unit
open import Cubical.HITs.S1 using () renaming (base to baseS1 ; loop to loopS1 ; toPropElim to S1-Ind-Prop)
open import Cubical.HITs.Sn
open import Cubical.ZCohomology.Groups.Prelims
open import Cubical.ZCohomology.Groups.Sn

private variable
  ℓ ℓ' : Level

open Iso

open CommRingStr (snd ℤCR) using ()
  renaming
  ( 0r        to 0ℤ
  ; 1r        to 1ℤ
  ; _+_       to _+ℤ_
  ; -_        to -ℤ_
  ; _·_       to _·ℤ_
  ; +Assoc    to +ℤAssoc
  ; +Identity to +ℤIdentity
  ; +Lid      to +ℤLid
  ; +Rid      to +ℤRid
  ; +Inv      to +ℤInv
  ; +Linv     to +ℤLinv
  ; +Rinv     to +ℤRinv
  ; +Comm     to +ℤComm
  ; ·Assoc    to ·ℤAssoc
  ; ·Identity to ·ℤIdentity
  ; ·Lid      to ·ℤLid
  ; ·Rid      to ·ℤRid
  ; ·Rdist+   to ·ℤRdist+
  ; ·Ldist+   to ·ℤLdist+
  ; is-set    to isSetℤ     )

open RingStr (snd (H*R (S₊ 1))) using ()
  renaming
  ( 0r        to 0H*
  ; 1r        to 1H*
  ; _+_       to _+H*_
  ; -_        to -H*_
  ; _·_       to _cup_
  ; +Assoc    to +H*Assoc
  ; +Identity to +H*Identity
  ; +Lid      to +H*Lid
  ; +Rid      to +H*Rid
  ; +Inv      to +H*Inv
  ; +Linv     to +H*Linv
  ; +Rinv     to +H*Rinv
  ; +Comm     to +H*Comm
  ; ·Assoc    to ·H*Assoc
  ; ·Identity to ·H*Identity
  ; ·Lid      to ·H*Lid
  ; ·Rid      to ·H*Rid
  ; ·Rdist+   to ·H*Rdist+
  ; ·Ldist+   to ·H*Ldist+
  ; is-set    to isSetH*     )

ℤ[X] : CommRing ℓ-zero
ℤ[X] = PolyCommRing ℤCR 1

ℤ[x] : Type ℓ-zero
ℤ[x] = fst ℤ[X]

open CommRingStr (snd ℤ[X]) using ()
  renaming
  ( 0r        to 0Pℤ
  ; 1r        to 1Pℤ
  ; _+_       to _+Pℤ_
  ; -_        to -Pℤ_
  ; _·_       to _·Pℤ_
  ; +Assoc    to +PℤAssoc
  ; +Identity to +PℤIdentity
  ; +Lid      to +PℤLid
  ; +Rid      to +PℤRid
  ; +Inv      to +PℤInv
  ; +Linv     to +PℤLinv
  ; +Rinv     to +PℤRinv
  ; +Comm     to +PℤComm
  ; ·Assoc    to ·PℤAssoc
  ; ·Identity to ·PℤIdentity
  ; ·Lid      to ·PℤLid
  ; ·Rid      to ·PℤRid
  ; ·Comm     to ·PℤComm
  ; ·Rdist+   to ·PℤRdist+
  ; ·Ldist+   to ·PℤLdist+
  ; is-set    to isSetPℤ     )



-----------------------------------------------------------------------------
-- Definitions

<X²> : FinVec ℤ[x] 1
<X²> zero = baseP (2 ∷ []) (CommRingStr.1r (snd ℤCR))

ℤ[X]/X² : CommRing ℓ-zero
ℤ[X]/X² = ℤ[X] / genIdeal ℤ[X] <X²>

ℤ[x]/x² : Type ℓ-zero
ℤ[x]/x² = fst ℤ[X]/X²

open CommRingStr (snd ℤ[X]/X²) using ()
  renaming
  ( 0r        to 0PℤI
  ; 1r        to 1PℤI
  ; _+_       to _+PℤI_
  ; -_        to -PℤI_
  ; _·_       to _·PℤI_
  ; +Assoc    to +PℤIAssoc
  ; +Identity to +PℤIIdentity
  ; +Lid      to +PℤILid
  ; +Rid      to +PℤIRid
  ; +Inv      to +PℤIInv
  ; +Linv     to +PℤILinv
  ; +Rinv     to +PℤIRinv
  ; +Comm     to +PℤIComm
  ; ·Assoc    to ·PℤIAssoc
  ; ·Identity to ·PℤIIdentity
  ; ·Lid      to ·PℤILid
  ; ·Rid      to ·PℤIRid
  ; ·Rdist+   to ·PℤIRdist+
  ; ·Ldist+   to ·PℤILdist+
  ; is-set    to isSetPℤI     )

-----------------------------------------------------------------------------
-- Direct Sens on ℤ[x]

ℤ[x]→H*-S¹ : ℤ[x] → H* (S₊ 1)
ℤ[x]→H*-S¹ = Poly-Rec-Set.f _ _ _ isSetH*
                0H*
                base-trad
                _+H*_
                +H*Assoc
                +H*Rid
                +H*Comm
                base-neutral-eq
                base-add-eq
             where
             base-trad : _
             base-trad (zero ∷ [])        a = base 0 (inv (fst (H⁰-Sⁿ≅ℤ 0)) a)
             base-trad (one ∷ [])         a = base 1 (inv (fst coHom1S1≃ℤ) a)
             base-trad (suc (suc n) ∷ []) a = 0H*

             base-neutral-eq :  _
             base-neutral-eq (zero ∷ [])        = cong (base 0) (IsGroupHom.pres1 (snd (invGroupIso (H⁰-Sⁿ≅ℤ 0)))) ∙ base-neutral _
             base-neutral-eq (one ∷ [])         = cong (base 1) (IsGroupHom.pres1 (snd (invGroupIso coHom1S1≃ℤ))) ∙ base-neutral _
             base-neutral-eq (suc (suc n) ∷ []) = refl

             base-add-eq : _
             base-add-eq (zero ∷ []) a b        = (base-add _ _ _) ∙ (cong (base 0) (sym (IsGroupHom.pres· (snd (invGroupIso (H⁰-Sⁿ≅ℤ 0))) a b)))
             base-add-eq (one ∷ []) a b         = (base-add _ _ _) ∙ (cong (base 1) (sym (IsGroupHom.pres· (snd (invGroupIso coHom1S1≃ℤ)) a b)))
             base-add-eq (suc (suc n) ∷ []) a b = +H*Rid _

ℤ[x]→H*-S¹-map1Pℤ : ℤ[x]→H*-S¹ (1Pℤ) ≡ 1H*
ℤ[x]→H*-S¹-map1Pℤ = refl

ℤ[x]→H*-S¹-gmorph : (x y : ℤ[x]) → ℤ[x]→H*-S¹ (x +Pℤ y) ≡ ℤ[x]→H*-S¹ x +H* ℤ[x]→H*-S¹ y
ℤ[x]→H*-S¹-gmorph x y = refl


-- Ring Morphism : need to define the functions on the quotient ring
rmorph-base-case-00 : (a : ℤ) → (b : ℤ) →
              ℤ[x]→H*-S¹ (baseP (0 ∷ []) a ·Pℤ baseP (0 ∷ []) b)
            ≡ ℤ[x]→H*-S¹ (baseP (0 ∷ []) a) cup ℤ[x]→H*-S¹ (baseP (0 ∷ []) b)
rmorph-base-case-00 a b = cong (base 0) (cong ∣_∣₂ (funExt (λ _ → same a b)))
  where
  same : (a b : ℤ) → a · b ≡ _·₀_ {0} a b
  same (pos zero)       b = refl
  same (pos (suc n))    b = cong (_+ℤ_ b) (same (pos n) b)
  same (negsuc zero)    b = sym (+ℤLid (-ℤ b))
  same (negsuc (suc n)) b = (+ℤComm _ _) ∙ (cong₂ _+ℤ_ (same _ _) (sym (+ℤLid _)))

T0 : (z : ℤ) → coHom 0 (S₊ 1)
T0 = λ z → inv (fst (H⁰-Sⁿ≅ℤ 0)) z

T1 : (z : ℤ) → coHom 1 (S₊ 1)
T1 = λ z → inv (fst coHom1S1≃ℤ) z

-- idea : use the fact that T1 is an morphism, that T0 simplifies + control on the level of unfolding
rmorph-base-case-01 : (a : ℤ) → (b : ℤ) →
        T1 (a ·ℤ b) ≡ (T0 a) ⌣ (T1 b)
rmorph-base-case-01 (pos zero)      b  = (IsGroupHom.pres1 (snd (invGroupIso coHom1S1≃ℤ)))
rmorph-base-case-01 (pos (suc n))    b = ((IsGroupHom.pres· (snd (invGroupIso coHom1S1≃ℤ)) b (pos n ·ℤ b)))
                                         ∙ (cong (λ X → (T1 b) +ₕ X) (rmorph-base-case-01 (pos n) b))
rmorph-base-case-01 (negsuc zero)    b = cong T1 (sym (+ℤLid (-ℤ b))) -- issue with the definition of ℤCommRing and ℤGroup
                                         ∙ IsGroupHom.presinv (snd (invGroupIso coHom1S1≃ℤ)) b

rmorph-base-case-01 (negsuc (suc n)) b = cong T1 (+ℤComm (-ℤ b) (negsuc n ·ℤ b)) -- ·ℤ and ·₀ are defined symetrically !
                                         ∙ IsGroupHom.pres· (snd (invGroupIso coHom1S1≃ℤ)) (negsuc n ·ℤ b) (-ℤ b)
                                          ∙ cong₂ _+ₕ_ (rmorph-base-case-01 (negsuc n) b)
                                                       (cong T1 (sym (+ℤLid (-ℤ b)))
                                                          ∙ IsGroupHom.presinv (snd (invGroupIso coHom1S1≃ℤ)) b)


rmorph-base-case-int : (n : ℕ) → (a : ℤ) → (m : ℕ) → (b : ℤ) →
              ℤ[x]→H*-S¹ (baseP (n ∷ []) a ·Pℤ baseP (m ∷ []) b)
            ≡ ℤ[x]→H*-S¹ (baseP (n ∷ []) a) cup ℤ[x]→H*-S¹ (baseP (m ∷ []) b)
rmorph-base-case-int zero          a zero          b = rmorph-base-case-00 a b
rmorph-base-case-int zero          a one           b = cong (base 1) (rmorph-base-case-01 a b)
rmorph-base-case-int zero          a (suc (suc m)) b = refl
rmorph-base-case-int one           a zero          b = cong ℤ[x]→H*-S¹ (·PℤComm (baseP (1 ∷ []) a) (baseP (zero ∷ []) b))
                                                       ∙ rmorph-base-case-int 0 b 1 a
                                                       ∙ gradCommRing (S₊ 1) 0 1 (inv (fst (H⁰-Sⁿ≅ℤ 0)) b) (inv (fst coHom1S1≃ℤ) a)
rmorph-base-case-int one           a one           b = sym (base-neutral 2) ∙
                                                       cong (base 2) (isOfHLevelRetractFromIso 1 (fst (Hⁿ-Sᵐ≅0 1 0 nsnotz)) isPropUnit _ _)
rmorph-base-case-int one           a (suc (suc m)) b = refl
rmorph-base-case-int (suc (suc n)) a m             b = refl

rmorph-base-case-vec : (v : Vec ℕ 1) → (a : ℤ) → (v' : Vec ℕ 1) → (b : ℤ) →
              ℤ[x]→H*-S¹ (baseP v a ·Pℤ baseP v' b)
            ≡ ℤ[x]→H*-S¹ (baseP v a) cup ℤ[x]→H*-S¹ (baseP v' b)
rmorph-base-case-vec (n ∷ []) a (m ∷ []) b = rmorph-base-case-int n a m b


ℤ[x]→H*-S¹-rmorph : (x y : ℤ[x]) → ℤ[x]→H*-S¹ (x ·Pℤ y) ≡ ℤ[x]→H*-S¹ x cup ℤ[x]→H*-S¹ y
ℤ[x]→H*-S¹-rmorph = Poly-Ind-Prop.f _ _ _
                       (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
                       (λ y → refl)
                       base-case
                       λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
  where
  base-case : _
  base-case (n ∷ []) a = Poly-Ind-Prop.f _ _ _ (λ _ → isSetH* _ _)
                         (sym (RingTheory.0RightAnnihilates (H*R (S₊ 1)) _))
                         (λ v' b → rmorph-base-case-vec (n ∷ []) a v' b)
                         λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*Rdist+ _ _ _)


-- Defining on the quotient
ℤ[x]→H*-S¹-cancelX : (k : Fin 1) → ℤ[x]→H*-S¹ (<X²> k) ≡ 0H*
ℤ[x]→H*-S¹-cancelX zero = refl

ℤ[X]→H*-S¹ : RingHom (CommRing→Ring ℤ[X]) (H*R (S₊ 1))
fst ℤ[X]→H*-S¹ = ℤ[x]→H*-S¹
snd ℤ[X]→H*-S¹ = makeIsRingHom ℤ[x]→H*-S¹-map1Pℤ ℤ[x]→H*-S¹-gmorph ℤ[x]→H*-S¹-rmorph

ℤ[X]/X²→H*R-S¹ : RingHom (CommRing→Ring ℤ[X]/X²) (H*R (S₊ 1))
ℤ[X]/X²→H*R-S¹ = Rec-Quotient-FGIdeal-Ring.f ℤ[X] (H*R (S₊ 1)) ℤ[X]→H*-S¹ <X²> ℤ[x]→H*-S¹-cancelX

ℤ[x]/x²→H*-S¹ : ℤ[x]/x² → H* (S₊ 1)
ℤ[x]/x²→H*-S¹ = fst ℤ[X]/X²→H*R-S¹



-- -----------------------------------------------------------------------------
-- -- Converse Sens on ℤ[X]



H*-S¹→ℤ[x] : H* (S₊ 1) → ℤ[x]
H*-S¹→ℤ[x] = DS-Rec-Set.f _ _ _ _ isSetPℤ
                0Pℤ
                base-trad
                _+Pℤ_
                +PℤAssoc
                +PℤRid
                +PℤComm
                base-neutral-eq
                base-add-eq
             where
             base-trad : _
             base-trad zero a          = baseP (0 ∷ []) (fun (fst (H⁰-Sⁿ≅ℤ 0)) a)
             base-trad one a           = baseP (1 ∷ []) (fun (fst coHom1S1≃ℤ) a)
             base-trad (suc (suc n)) a = 0Pℤ

             base-neutral-eq : _
             base-neutral-eq zero          = cong (baseP (0 ∷ [])) (IsGroupHom.pres1 (snd (H⁰-Sⁿ≅ℤ 0))) ∙ base-0P _
             base-neutral-eq one           = cong (baseP (1 ∷ [])) (IsGroupHom.pres1 (snd coHom1S1≃ℤ)) ∙ base-0P _
             base-neutral-eq (suc (suc n)) = refl

             base-add-eq : _
             base-add-eq zero a b        = (base-Poly+ _ _ _) ∙ (cong (baseP (0 ∷ [])) (sym (IsGroupHom.pres· (snd (H⁰-Sⁿ≅ℤ 0)) a b)))
             base-add-eq one a b         = (base-Poly+ _ _ _) ∙ (cong (baseP (1 ∷ [])) (sym (IsGroupHom.pres· (snd coHom1S1≃ℤ) a b)))
             base-add-eq (suc (suc n)) a b = +PℤRid _

H*-S¹→ℤ[x]-gmorph : (x y : H* (S₊ 1)) → H*-S¹→ℤ[x] ( x +H* y) ≡ H*-S¹→ℤ[x] x +Pℤ H*-S¹→ℤ[x] y
H*-S¹→ℤ[x]-gmorph x y = refl

H*-S¹→ℤ[x]/x² : H* (S₊ 1) → ℤ[x]/x²
H*-S¹→ℤ[x]/x² = [_] ∘ H*-S¹→ℤ[x]

H*-S¹→ℤ[x]/x²-gmorph : (x y : H* (S₊ 1)) → H*-S¹→ℤ[x]/x² (x +H* y) ≡ (H*-S¹→ℤ[x]/x² x) +PℤI (H*-S¹→ℤ[x]/x² y)
H*-S¹→ℤ[x]/x²-gmorph x y = refl



-- -----------------------------------------------------------------------------
-- -- Section

e-sect : (x : ℤ[x]/x²) → H*-S¹→ℤ[x]/x² (ℤ[x]/x²→H*-S¹ x) ≡ x
e-sect = elimProp-sq (λ _ → isSetPℤI _ _)
         (Poly-Ind-Prop.f _ _ _ (λ _ → isSetPℤI _ _)
         refl
         base-case
         λ {U V} ind-U ind-V → cong₂ _+PℤI_ ind-U ind-V)
         where
         base-case : _
         base-case (zero ∷ [])        a = cong [_] (cong (baseP (0 ∷ [])) (rightInv (fst (H⁰-Sⁿ≅ℤ 0)) a))
         base-case (one ∷ [])         a = cong [_] (cong (baseP (1 ∷ [])) (rightInv (fst coHom1S1≃ℤ) a))
         base-case (suc (suc n) ∷ []) a = eq/ 0Pℤ (baseP (suc (suc n) ∷ []) a) ∣ ((λ x → baseP (n ∷ []) (-ℤ a)) , helper) ∣₋₁
           where
           helper : _
           helper = (+PℤLid _) ∙ cong₂ baseP (cong (λ X → X ∷ []) (sym (+-comm n 2))) (sym (·ℤRid _)) ∙ (sym (+PℤRid _))

-- -----------------------------------------------------------------------------
-- -- Retraction

e-retr : (x : H* (S₊ 1)) → ℤ[x]/x²→H*-S¹ (H*-S¹→ℤ[x]/x² x) ≡ x
e-retr = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
         refl
         base-case
         λ {U V} ind-U ind-V → cong₂ _+H*_ ind-U ind-V
         where
         base-case : _
         base-case zero          a = cong (base 0) (leftInv (fst (H⁰-Sⁿ≅ℤ 0)) a)
         base-case one           a = cong (base 1) (leftInv (fst coHom1S1≃ℤ) a)
         base-case (suc (suc n)) a = (sym (base-neutral (suc (suc n))))
                                     ∙ cong (base (suc (suc n))) (isOfHLevelRetractFromIso 1 (fst (Hⁿ-Sᵐ≅0 (suc n) 0 nsnotz)) isPropUnit _ _)
