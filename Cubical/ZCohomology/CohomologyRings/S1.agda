{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.S1 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
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

open import Cubical.HITs.Sn
open import Cubical.ZCohomology.Groups.Sn

private variable
  ℓ : Level

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

-- Complicated proof to specialised
-- ℤ[x]→H*-Unit-rmorph : (x y : ℤ[x]) → ℤ[x]→H*-Unit (x ·Pℤ y) ≡ ℤ[x]→H*-Unit x cup ℤ[x]→H*-Unit y
-- ℤ[x]→H*-Unit-rmorph =
--       Poly-Ind-Prop.f _ _ _
--          (λ P p q i y j → isSetH* _ _ (p y) (q y) i j)
--          (λ y → refl)
--          base-case
--          λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
--            where
--            base-case : _
--            base-case (zero ∷ []) a =
--              Poly-Ind-Prop.f _ _ _ (λ _ → isSetH* _ _)
--              refl
--              base-case'
--              (λ {U V} ind-U ind-V → cong₂ _+H*_ ind-U ind-V)
--                where
--                base-case' : _
--                base-case' (zero ∷ []) b = cong (base 0) (cong  ∣_∣₂ (same a b))
--                  where
--                  same : (x y : ℤ) → (λ _ → x ·ℤ y) ≡ (λ x₁ → x ·₀ y)
--                  same (pos zero) y = refl
--                  same (pos (suc n)) y = funExt (λ z → cong (y +ℤ_) λ i → same (pos n) y i z)
--                  same (negsuc zero) y = funExt (λ z  → sym (+ℤLid (negsuc zero ·ℤ y)))
--                  same (negsuc (suc n)) y = funExt (λ z → (+ℤComm _ _)
--                                            ∙ cong₂ _+ℤ_ (λ i → same (negsuc n) y i z) (sym (+ℤLid (negsuc zero ·ℤ y))))
--                base-case' (suc x ∷ []) b = refl
--            base-case (suc n ∷ []) a =
--              Poly-Ind-Prop.f _ _ _ (λ _ → isSetH* _ _)
--              refl
--              base-case'
--              (λ {U V} ind-U ind-V → cong₂ _+H*_ ind-U ind-V ∙ +H*Rid _)
--                where
--                base-case' : _
--                base-case' (zero ∷ []) b = refl
--                base-case' (suc n ∷ []) b = refl


ℤ[x]→H*-S¹-cancelX : (k : Fin 1) → ℤ[x]→H*-S¹ (<X²> k) ≡ 0H*
ℤ[x]→H*-S¹-cancelX zero = refl

-- ℤ[X]→H*-S¹ : RingHom (CommRing→Ring ℤ[X]) (H*R S¹)
-- fst ℤ[X]→H*-S¹ = ℤ[x]→H*-S¹
-- snd ℤ[X]→H*-S¹ = makeIsRingHom ℤ[x]→H*-S¹-map1Pℤ ℤ[x]→H*-S¹-gmorph ℤ[x]→H*-S¹-rmorph

-- ℤ[X]/X→H*R-S¹ : RingHom (CommRing→Ring ℤ[X]/X) (H*R S¹)
-- ℤ[X]/X→H*R-S¹ = Rec-Quotient-FGIdeal-Ring.f ℤ[X] (H*R S¹) ℤ[X]→H*-S¹ <X²> ℤ[x]→H*-S¹-cancelX

-- ℤ[x]/x→H*-S¹ : ℤ[x]/x → H* S¹
-- ℤ[x]/x→H*-S¹ = fst ℤ[X]/X→H*R-S¹



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
H*-S¹→ℤ[x]/x²-gmorph x y = cong [_] (H*-S¹→ℤ[x]-gmorph x y)



-- -----------------------------------------------------------------------------
-- -- Section

-- e-sect : (x : ℤ[x]/x) → H*-Unit→ℤ[x]/x (ℤ[x]/x→H*-Unit x) ≡ x
-- e-sect = elimProp-sq (λ _ → isSetPℤI _ _)
--          (Poly-Ind-Prop.f _ _ _ (λ _ → isSetPℤI _ _)
--          refl
--          base-case
--          λ {U V} ind-U ind-V → cong₂ _+PℤI_ ind-U ind-V)
--          where
--          base-case : _
--          base-case (zero ∷ []) a = refl
--          base-case (suc n ∷ []) a = eq/ 0Pℤ (baseP (suc n ∷ []) a) ∣ ((λ x → baseP (n ∷ []) (-ℤ a)) , foo) ∣₋₁
--            where
--            foo : (0P Poly+ baseP (suc n ∷ []) (- a)) ≡ (baseP (n +n 1 ∷ []) (- a · pos 1) Poly+ 0P)
--            foo = (0P Poly+ baseP (suc n ∷ []) (- a)) ≡⟨ +PℤLid _ ⟩
--                  baseP (suc n ∷ []) (- a) ≡⟨ cong₂ baseP (cong (λ X → X ∷ []) (sym ((+-suc n 0)
--                                             ∙ (cong suc (+-zero n))))) (sym (·ℤRid _)) ⟩
--                  baseP (n +n suc 0 ∷ []) (- a ·ℤ 1ℤ) ≡⟨ refl ⟩
--                  baseP (n +n 1 ∷ []) (- a · pos 1) ≡⟨ sym (+PℤRid _) ⟩
--                  (baseP (n +n 1 ∷ []) (- a · pos 1) Poly+ 0P) ∎



-- -----------------------------------------------------------------------------
-- -- Retraction

-- e-retr : (x : H* Unit) → ℤ[x]/x→H*-Unit (H*-Unit→ℤ[x]/x x) ≡ x
-- e-retr = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
--          refl
--          base-case
--          λ {U V} ind-U ind-V → cong ℤ[x]/x→H*-Unit (H*-Unit→ℤ[x]/x-gmorph U V)
--                                 ∙ IsRingHom.pres+ (snd ℤ[X]/X→H*R-Unit) (H*-Unit→ℤ[x]/x U) (H*-Unit→ℤ[x]/x V)
--                                 ∙ cong₂ _+H*_ ind-U ind-V
--          where
--          base-case : _
--          base-case zero a = cong (base 0) (leftInv (fst H⁰-Unit≅ℤ) a)
--          base-case (suc n) a = (sym (base-neutral (suc n)))
--                                ∙ (cong (base (suc n)) ((isContr→isProp (isContrHⁿ-Unit n) _ a)))
