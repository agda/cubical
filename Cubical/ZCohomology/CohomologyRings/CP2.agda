
{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.CP2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty renaming (rec to rec-⊥ ; elim to elim-⊥)
open import Cubical.Data.Nat renaming (_+_ to _+n_ ; +-comm to +n-comm ; _·_ to _·n_ ; snotz to nsnotz ; znots to nznots)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Vec
open import Cubical.Data.FinData

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group hiding (UnitGroup₀ ; Bool ; _/_ ) renaming (ℤ to ℤG)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤ to ℤCR)
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.QuotientRing
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly-Quotient

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
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.CohomologyRing
open import Cubical.ZCohomology.CohomologyRings.Eliminator-Poly-Quotient-to-Ring

open import Cubical.Data.Unit
open import Cubical.ZCohomology.Groups.CP2

private variable
  ℓ ℓ' : Level

open Iso


-----------------------------------------------------------------------------
-- Somme properties over H⁰-Sⁿ≅ℤ
module Properties-H⁰CP²≅ℤ where

  open RingStr

  T0 : (z : ℤ) → coHomGr 0 CP² .fst
  T0 = inv (fst H⁰CP²≅ℤ)

  T0g : IsGroupHom (snd ℤG) T0 (coHomGr 0 CP² .snd)
  T0g = snd (invGroupIso H⁰CP²≅ℤ)

  T0-pos0 : {l : ℕ} → (x : coHom l CP²) → T0 (pos zero) ⌣ x ≡ 0ₕ l
  T0-pos0 = sElim (λ _ → isProp→isSet (squash₂ _ _)) (λ _ → refl)

  T0-posS : {l : ℕ} → (k : ℕ) → (x : coHom l CP²)
            → T0 (pos (suc k)) ⌣ x ≡ x +ₕ (T0 (pos k) ⌣ x)
  T0-posS k = sElim (λ x → isProp→isSet (squash₂ _ _)) (λ _ → refl)

  T0-neg0 : {l : ℕ} → (x : coHom l CP²) → T0 (negsuc zero) ⌣ x ≡ -ₕ x
  T0-neg0 = sElim (λ x → isProp→isSet (squash₂ _ _)) (λ _ → refl)

  T0-negS : {l : ℕ} → (k : ℕ) → (x : coHom l CP²)
            → T0 (negsuc (suc k)) ⌣ x ≡ (T0 (negsuc k) ⌣ x) +ₕ (-ₕ x)
  T0-negS k = sElim (λ x → isProp→isSet (squash₂ _ _)) (λ x → refl)



-----------------------------------------------------------------------------
-- Definitions

module Equiv-CP2-Properties where

  open IsGroupHom
  open Properties-H⁰CP²≅ℤ

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

  open RingStr (snd (H*R CP²)) using ()
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

  open CommRingStr (snd ℤ[X]/X³) using ()
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
-- Partition of ℕ

  data partℕ (k : ℕ) : Type ℓ-zero where
    is0  : (k ≡ 0)            → partℕ k
    is2  : (k ≡ 2)            → partℕ k
    is4  : (k ≡ 4)            → partℕ k
    else : (k ≡ 0 → ⊥)
           × ((k ≡ 2 → ⊥)
              × (k ≡ 4 → ⊥)) → partℕ k

  part : (k : ℕ) → partℕ k
  part k with (discreteℕ k 0)
  ... | yes p = is0 p
  ... | no ¬p with (discreteℕ k 2)
  ... |       yes q = is2 q
  ... |       no ¬q with (discreteℕ k 4)
  ... |             yes r = is4 r
  ... |             no ¬r = else (¬p , (¬q , ¬r))


  part0 : part 0 ≡ is0 refl
  part0 = refl

  part2 : part 2 ≡ is2 refl
  part2 = refl

  part4 : part 4 ≡ is4 refl
  part4 = refl



-----------------------------------------------------------------------------
-- As we are in the general case, the definition are now up to a path and not definitional
-- Hence when need to add transport to go from coHom 0 X to coHom 0 X
-- This some notation and usefull lemma

  SubstCoHom : {k l : ℕ} → (x : k ≡ l) → (a : coHom k CP²) → coHom l CP²
  SubstCoHom x a = subst (λ X → coHom X CP²) x a

  -- solve a pbl of project with the notation
  SubstReflCoHom : {k : ℕ} → (a : coHom k CP²) → subst (λ X → coHom X CP²) refl a ≡ a
  SubstReflCoHom a = substRefl a

  subst-0 : (k l : ℕ) → (x : k ≡ l) → SubstCoHom x (0ₕ k) ≡ 0ₕ l
  subst-0 k l x = J (λ l x → SubstCoHom x (0ₕ k) ≡ 0ₕ l) (SubstReflCoHom (0ₕ k)) x

  subst-+ : (k : ℕ) → (a b : coHom k CP²) → (l : ℕ) → (x : k ≡ l)
            → SubstCoHom x (a +ₕ b) ≡ SubstCoHom x a +ₕ SubstCoHom x b
  subst-+ k a b l x = J (λ l x → SubstCoHom x (a +ₕ b) ≡ SubstCoHom x a +ₕ SubstCoHom x b)
                        (SubstReflCoHom (a +ₕ b) ∙ sym (cong₂ _+ₕ_ (SubstReflCoHom a) (SubstReflCoHom b)))
                        x

  subst-⌣ : (k : ℕ) → (a b : coHom k CP²) → (l : ℕ) → (x : k ≡ l)
            → SubstCoHom (cong₂ _+'_ x x) (a ⌣ b) ≡ SubstCoHom x a ⌣ SubstCoHom x b
  subst-⌣ k a b l x = J (λ l x → SubstCoHom (cong₂ _+'_ x x) (a ⌣ b) ≡ SubstCoHom x a ⌣ SubstCoHom x b)
                        (SubstReflCoHom (a ⌣ b) ∙ sym (cong₂ _⌣_ (SubstReflCoHom a) (SubstReflCoHom b)))
                        x



-----------------------------------------------------------------------------
-- Direct Sens on ℤ[x]

  ℤ[x]→H*-CP² : ℤ[x] → H* CP²
  ℤ[x]→H*-CP² = Poly-Rec-Set.f _ _ _ isSetH*
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
    base-trad (zero ∷ []) a = base 0 (inv (fst H⁰CP²≅ℤ) a)
    base-trad (one ∷ []) a  = base 2 (inv (fst H²CP²≅ℤ) a)
    base-trad (two ∷ []) a  = base 4 (inv (fst H⁴CP²≅ℤ) a)
    base-trad (suc (suc (suc k)) ∷ []) a = 0H*

    base-neutral-eq : _
    base-neutral-eq (zero ∷ []) = cong (base 0) (pres1 (snd (invGroupIso H⁰CP²≅ℤ))) ∙ base-neutral _
    base-neutral-eq (one ∷ [])  = cong (base 2) (pres1 (snd (invGroupIso H²CP²≅ℤ))) ∙ base-neutral _
    base-neutral-eq (two ∷ [])  = cong (base 4) (pres1 (snd (invGroupIso H⁴CP²≅ℤ))) ∙ base-neutral _
    base-neutral-eq (suc (suc (suc k)) ∷ []) = refl

    base-add-eq : _
    base-add-eq (zero ∷ []) a b = base-add _ _ _ ∙ cong (base 0) (sym (pres· (snd (invGroupIso H⁰CP²≅ℤ)) a b))
    base-add-eq (one ∷ []) a b  = base-add _ _ _ ∙ cong (base 2) (sym (pres· (snd (invGroupIso H²CP²≅ℤ)) a b))
    base-add-eq (two ∷ []) a b  = base-add _ _ _ ∙ cong (base 4) (sym (pres· (snd (invGroupIso H⁴CP²≅ℤ)) a b))
    base-add-eq (suc (suc (suc k)) ∷ []) a b = +H*Rid _


-----------------------------------------------------------------------------
-- Morphism on ℤ[x]

  ℤ[x]→H*-CP²-map1 : ℤ[x]→H*-CP² (1Pℤ) ≡ 1H*
  ℤ[x]→H*-CP²-map1 = refl

  ℤ[x]→H*-CP²-map+ : (x y : ℤ[x]) → ℤ[x]→H*-CP² (x +Pℤ y) ≡ ℤ[x]→H*-CP² x +H* ℤ[x]→H*-CP² y
  ℤ[x]→H*-CP²-map+ x y = refl

-- cup product on H⁰ → Hⁿ → Hⁿ
  module _
    (l : ℕ)
    (Tl : (z : ℤ) → coHom l CP²)
    (Tlg : IsGroupHom (ℤG .snd) Tl (coHomGr l CP² .snd))
    where

      rmorph-base-case-0l : (a : ℤ) → (b : ℤ) →
                            Tl (a ·ℤ b) ≡ (T0 a) ⌣ (Tl b)
      rmorph-base-case-0l (pos zero)       b = pres1 Tlg
                                               ∙ sym (T0-pos0 (Tl b))
      rmorph-base-case-0l (pos (suc k))    b = pres· Tlg b (pos k ·ℤ b)
                                               ∙ cong (λ X → (Tl b) +ₕ X) (rmorph-base-case-0l (pos k) b)
                                               ∙ sym (T0-posS k (Tl b))
      rmorph-base-case-0l (negsuc zero)    b = cong Tl (sym (+ℤLid (-ℤ b)))
                                               ∙ presinv Tlg b
                                               ∙ sym (T0-neg0 (Tl b))
      rmorph-base-case-0l (negsuc (suc k)) b = cong Tl (+ℤComm (-ℤ b) (negsuc k ·ℤ b))
                                               ∙ pres· Tlg (negsuc k ·ℤ b) (-ℤ b)
                                               ∙ cong₂ _+ₕ_ (rmorph-base-case-0l (negsuc k) b)
                                                            (cong Tl (sym (+ℤLid (-ℤ b))) ∙ presinv Tlg b)
                                               ∙ sym (T0-negS k (Tl b))

  rmorph-base-case-11 : (a b : ℤ) → inv (fst H⁴CP²≅ℤ) (a ·ℤ b) ≡  inv (fst H²CP²≅ℤ) a ⌣ inv (fst H²CP²≅ℤ) b
  rmorph-base-case-11 (pos zero) (pos zero) = {!!}
  rmorph-base-case-11 (pos zero) (pos (suc n₁)) = {!!}
  rmorph-base-case-11 (pos (suc n)) (pos zero) = {!!}
  rmorph-base-case-11 (pos (suc n)) (pos (suc n₁)) = {!!}
  rmorph-base-case-11 (pos n) (negsuc n₁) = {!!}
  rmorph-base-case-11 (negsuc n) (pos n₁) = {!!}
  rmorph-base-case-11 (negsuc n) (negsuc n₁) = {!!}



-- Nice packging of the proof

  rmorph-base-case-int : (k : ℕ) → (a : ℤ) → (l : ℕ) → (b : ℤ) →
                         ℤ[x]→H*-CP² (baseP (k ∷ []) a ·Pℤ baseP (l ∷ []) b)
                         ≡ ℤ[x]→H*-CP² (baseP (k ∷ []) a) cup ℤ[x]→H*-CP² (baseP (l ∷ []) b)
  rmorph-base-case-int zero a zero b = cong (base 0) (rmorph-base-case-0l 0 (inv (fst H⁰CP²≅ℤ)) (snd (invGroupIso H⁰CP²≅ℤ)) a b)
  rmorph-base-case-int zero a one b  = cong (base 2) (rmorph-base-case-0l 2 (inv (fst H²CP²≅ℤ)) (snd (invGroupIso H²CP²≅ℤ)) a b)
  rmorph-base-case-int zero a two b  = cong (base 4) (rmorph-base-case-0l 4 (inv (fst H⁴CP²≅ℤ)) (snd (invGroupIso H⁴CP²≅ℤ)) a b)
  rmorph-base-case-int zero a (suc (suc (suc l))) b = refl
  rmorph-base-case-int one a zero b = cong ℤ[x]→H*-CP² (·PℤComm (baseP (one ∷ []) a) (baseP (zero ∷ []) b))
                                      ∙ rmorph-base-case-int zero b one a
                                       ∙ gradCommRing CP² _ _ _ _
  rmorph-base-case-int one a one b  = cong (base 4) (rmorph-base-case-11 a b)
  rmorph-base-case-int one a two b  = sym (base-neutral _)
                                      ∙ cong (base 6) (isOfHLevelRetractFromIso 1 (fst (Hⁿ-CP²≅0 5 (compute-eqℕ _ _) (compute-eqℕ _ _))) isPropUnit _ _)
  rmorph-base-case-int one a (suc (suc (suc l))) b = refl
  rmorph-base-case-int two a zero b = cong ℤ[x]→H*-CP² (·PℤComm (baseP (two ∷ []) a) (baseP (zero ∷ []) b))
                                      ∙ rmorph-base-case-int zero b two a
                                       ∙ gradCommRing CP² _ _ _ _
  rmorph-base-case-int two a one b  = sym (base-neutral _)
                                      ∙ cong (base 6) (isOfHLevelRetractFromIso 1 (fst (Hⁿ-CP²≅0 5 (compute-eqℕ _ _) (compute-eqℕ _ _))) isPropUnit _ _)
  rmorph-base-case-int two a two b  = sym (base-neutral _)
                                      ∙ cong (base 8) (isOfHLevelRetractFromIso 1 (fst (Hⁿ-CP²≅0 7 (compute-eqℕ _ _) (compute-eqℕ _ _))) isPropUnit _ _)
  rmorph-base-case-int two a (suc (suc (suc l))) b = refl
  rmorph-base-case-int (suc (suc (suc k))) a l b = refl


  rmorph-base-case-vec : (v : Vec ℕ 1) → (a : ℤ) → (v' : Vec ℕ 1) → (b : ℤ) →
                ℤ[x]→H*-CP² (baseP v a ·Pℤ baseP v' b)
              ≡ ℤ[x]→H*-CP² (baseP v a) cup ℤ[x]→H*-CP² (baseP v' b)
  rmorph-base-case-vec (k ∷ []) a (l ∷ []) b = rmorph-base-case-int k a l b

  -- proof of the morphism
  ℤ[x]→H*-CP²-rmorph : (x y : ℤ[x]) → ℤ[x]→H*-CP² (x ·Pℤ y) ≡ ℤ[x]→H*-CP² x cup ℤ[x]→H*-CP² y
  ℤ[x]→H*-CP²-rmorph = Poly-Ind-Prop.f _ _ _
                         (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
                         (λ y → refl)
                         base-case
                         λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
    where
    base-case : _
    base-case (k ∷ []) a = Poly-Ind-Prop.f _ _ _ (λ _ → isSetH* _ _)
                           (sym (RingTheory.0RightAnnihilates (H*R CP²) _))
                           (λ v' b → rmorph-base-case-vec (k ∷ []) a v' b)
                           λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*Rdist+ _ _ _)


-----------------------------------------------------------------------------
-- Function on ℤ[x]/x + morphism

  ℤ[x]→H*-CP²-cancelX : (k : Fin 1) → ℤ[x]→H*-CP² (<X³> k) ≡ 0H*
  ℤ[x]→H*-CP²-cancelX zero = refl

  ℤ[X]→H*-CP² : RingHom (CommRing→Ring ℤ[X]) (H*R CP²)
  fst ℤ[X]→H*-CP² = ℤ[x]→H*-CP²
  snd ℤ[X]→H*-CP² = makeIsRingHom ℤ[x]→H*-CP²-map1 ℤ[x]→H*-CP²-map+ ℤ[x]→H*-CP²-rmorph

  ℤ[X]/X³→H*R-CP² : RingHom (CommRing→Ring ℤ[X]/X³) (H*R CP²)
  ℤ[X]/X³→H*R-CP² = Rec-Quotient-FGIdeal-Ring.f ℤ[X] (H*R CP²) ℤ[X]→H*-CP² <X³> ℤ[x]→H*-CP²-cancelX

  ℤ[x]/x³→H*-CP² : ℤ[x]/x³ → H* CP²
  ℤ[x]/x³→H*-CP² = fst ℤ[X]/X³→H*R-CP²



-----------------------------------------------------------------------------
-- Converse Sens on ℤ[X] + ℤ[x]/x

  base-trad-H* : (k : ℕ) → (a : coHom k CP²) → (x : partℕ k) → ℤ[x]
  base-trad-H* k a (is0 x) = baseP (0 ∷ []) (fun (fst H⁰CP²≅ℤ) (SubstCoHom x a))
  base-trad-H* k a (is2 x) = baseP (1 ∷ []) (fun (fst H²CP²≅ℤ) (SubstCoHom x a))
  base-trad-H* k a (is4 x) = baseP (2 ∷ []) (fun (fst H⁴CP²≅ℤ) (SubstCoHom x a))
  base-trad-H* k a (else x) = 0Pℤ

  H*-CP²→ℤ[x] : H* CP² → ℤ[x]
  H*-CP²→ℤ[x] = DS-Rec-Set.f _ _ _ _ isSetPℤ
       0Pℤ
       (λ k a → base-trad-H* k a (part k))
       _+Pℤ_
       +PℤAssoc
       +PℤRid
       +PℤComm
       (λ k → base-neutral-eq k (part k))
       λ k a b → base-add-eq k a b (part k)
    where

    base-neutral-eq : (k : ℕ) → (x : partℕ k) → base-trad-H* k (0ₕ k) x ≡ 0Pℤ
    base-neutral-eq k (is0 x) = cong (baseP (0 ∷ [])) (cong (fun (fst H⁰CP²≅ℤ)) (subst-0 k 0 x))
                                ∙ cong (baseP (0 ∷ [])) (pres1 (snd H⁰CP²≅ℤ))
                                ∙ base-0P (0 ∷ [])
    base-neutral-eq k (is2 x) = cong (baseP (1 ∷ [])) (cong (fun (fst H²CP²≅ℤ)) (subst-0 k 2 x))
                                ∙ cong (baseP (1 ∷ [])) (pres1 (snd H²CP²≅ℤ))
                                ∙ base-0P (1 ∷ [])
    base-neutral-eq k (is4 x) = cong (baseP (2 ∷ [])) (cong (fun (fst H⁴CP²≅ℤ)) (subst-0 k 4 x))
                                ∙ cong (baseP (2 ∷ [])) (pres1 (snd H⁴CP²≅ℤ))
                                ∙ base-0P (2 ∷ [])
    base-neutral-eq k (else x) = refl


    base-add-eq : (k : ℕ) → (a b : coHom k CP²) → (x : partℕ k)
                  → base-trad-H* k a x +Pℤ base-trad-H* k b x ≡ base-trad-H* k (a +ₕ b) x
    base-add-eq k a b (is0 x) = base-Poly+ _ _ _
                                ∙ cong (baseP (0 ∷ [])) (sym (pres· (snd H⁰CP²≅ℤ) _ _))
                                ∙ cong (baseP (0 ∷ [])) (cong (fun (fst H⁰CP²≅ℤ)) (sym (subst-+ k a b 0 x)))
    base-add-eq k a b (is2 x) = base-Poly+ _ _ _
                                ∙ cong (baseP (1 ∷ [])) (sym (pres· (snd H²CP²≅ℤ) _ _))
                                ∙ cong (baseP (1 ∷ [])) (cong (fun (fst H²CP²≅ℤ)) (sym (subst-+ k a b 2 x)))
    base-add-eq k a b (is4 x) = base-Poly+ _ _ _
                                ∙ cong (baseP (2 ∷ [])) (sym (pres· (snd H⁴CP²≅ℤ) _ _))
                                ∙ cong (baseP (2 ∷ [])) (cong (fun (fst H⁴CP²≅ℤ)) (sym (subst-+ k a b 4 x)))
    base-add-eq k a b (else x) = +PℤRid _

  H*-CP²→ℤ[x]-gmorph : (x y : H* CP²) → H*-CP²→ℤ[x] ( x +H* y) ≡ H*-CP²→ℤ[x] x +Pℤ H*-CP²→ℤ[x] y
  H*-CP²→ℤ[x]-gmorph x y = refl

  H*-CP²→ℤ[x]/x³ : H* CP² → ℤ[x]/x³
  H*-CP²→ℤ[x]/x³ = [_] ∘ H*-CP²→ℤ[x]

  H*-CP²→ℤ[x]/x³-gmorph : (x y : H* CP²) → H*-CP²→ℤ[x]/x³ (x +H* y) ≡ (H*-CP²→ℤ[x]/x³ x) +PℤI (H*-CP²→ℤ[x]/x³ y)
  H*-CP²→ℤ[x]/x³-gmorph x y = refl



-----------------------------------------------------------------------------
-- Section

  e-sect-base : (k : ℕ) → (a : coHom k CP²) → (x : partℕ k) →
                ℤ[x]/x³→H*-CP² [ (base-trad-H* k a x) ] ≡ base k a
  e-sect-base k a (is0 x) = cong (base 0) (leftInv (fst H⁰CP²≅ℤ) (SubstCoHom x a))
                            ∙ sym (ConstsubstCommSlice (λ x → coHom x CP²) (H* CP²) base x a)
  e-sect-base k a (is2 x) = cong (base 2) (leftInv (fst H²CP²≅ℤ) (SubstCoHom x a))
                            ∙ sym (ConstsubstCommSlice (λ x → coHom x CP²) (H* CP²) base x a)
  e-sect-base k a (is4 x) = cong (base 4) (leftInv (fst H⁴CP²≅ℤ) (SubstCoHom x a))
                            ∙ sym (ConstsubstCommSlice (λ x → coHom x CP²) (H* CP²) base x a)
  e-sect-base k a (else x) = sym (base-neutral k)
                             ∙ ConstsubstCommSlice ((λ x → coHom x CP²)) ((H* CP²)) base (suc-predℕ k (fst x)) (0ₕ k)
                             ∙ cong (base (suc (predℕ k)))
                                    (((isOfHLevelRetractFromIso 1
                                         (fst (Hⁿ-CP²≅0 (predℕ k)
                                                        (λ p → fst (snd x) (suc-predℕ k (fst x) ∙ p))
                                                        λ p → snd (snd x) (suc-predℕ k (fst x) ∙ p)) )
                                         isPropUnit _ _)))
                             ∙ sym (ConstsubstCommSlice ((λ x → coHom x CP²)) ((H* CP²)) base (suc-predℕ k (fst x)) a)

  e-sect : (x : H* CP²) → ℤ[x]/x³→H*-CP² (H*-CP²→ℤ[x]/x³ x) ≡ x
  e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
           refl
           (λ k a → e-sect-base k a (part k))
           λ {U V} ind-U ind-V → cong₂ _+H*_ ind-U ind-V


-----------------------------------------------------------------------------
-- Retraction

  e-retr : (x : ℤ[x]/x³) → H*-CP²→ℤ[x]/x³ (ℤ[x]/x³→H*-CP² x) ≡ x
  e-retr = elimProp-sq (λ _ → isSetPℤI _ _)
           (Poly-Ind-Prop.f _ _ _ (λ _ → isSetPℤI _ _)
           refl
           base-case
           λ {U V} ind-U ind-V → cong₂ _+PℤI_ ind-U ind-V)
           where
           base-case : _
           base-case (zero ∷ []) a = cong [_] (cong (baseP (0 ∷ [])) (cong (fun (fst H⁰CP²≅ℤ))
                                                                               (SubstReflCoHom (inv (fst H⁰CP²≅ℤ) a))))
                                    ∙ cong [_] (cong (baseP (0 ∷ [])) (rightInv (fst H⁰CP²≅ℤ) a))
           base-case (one ∷ []) a = cong [_] (cong (baseP (1 ∷ [])) (cong (fun (fst H²CP²≅ℤ))
                                                                               (SubstReflCoHom (inv (fst H²CP²≅ℤ) a))))
                                    ∙ cong [_] (cong (baseP (1 ∷ [])) (rightInv (fst H²CP²≅ℤ) a))
           base-case (two ∷ []) a = cong [_] (cong (baseP (2 ∷ [])) (cong (fun (fst H⁴CP²≅ℤ))
                                                                               (SubstReflCoHom (inv (fst H⁴CP²≅ℤ) a))))
                                    ∙ cong [_] (cong (baseP (2 ∷ [])) (rightInv (fst H⁴CP²≅ℤ) a))
           base-case (suc (suc (suc k)) ∷ []) a = eq/ 0Pℤ (baseP (suc (suc (suc k)) ∷ []) a)  ∣ ((λ x → baseP (k ∷ []) (-ℤ a)) , helper) ∣₋₁
             where
             helper : _
             helper = (+PℤLid _) ∙ cong₂ baseP (cong (λ X → X ∷ []) (sym (+n-comm k 3))) (sym (·ℤRid _)) ∙ (sym (+PℤRid _))



-----------------------------------------------------------------------------
-- Computation of the Cohomology Ring

module _ where

  open Equiv-CP2-Properties

  CP²-CohomologyRing : RingEquiv (CommRing→Ring ℤ[X]/X³) (H*R CP²)
  fst CP²-CohomologyRing = isoToEquiv is
    where
    is : Iso ℤ[x]/x³ (H* CP²)
    fun is = ℤ[x]/x³→H*-CP²
    inv is = H*-CP²→ℤ[x]/x³
    rightInv is = e-sect
    leftInv is = e-retr
  snd CP²-CohomologyRing = snd ℤ[X]/X³→H*R-CP²

  CohomologyRing-CP² : RingEquiv (H*R CP²) (CommRing→Ring ℤ[X]/X³)
  CohomologyRing-CP² = RingEquivs.invEquivRing CP²-CohomologyRing
