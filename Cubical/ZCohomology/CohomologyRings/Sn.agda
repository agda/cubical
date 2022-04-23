{-# OPTIONS --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.Sn where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty renaming (rec to rec-⊥ ; elim to elim-⊥)
open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_ ; snotz to nsnotz)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Vec
open import Cubical.Data.FinData

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group hiding (Unit ; Bool ; _/_ ) renaming (ℤ to ℤG)
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
open import Cubical.ZCohomology.RingStructure.CohomologyRing
open import Cubical.ZCohomology.CohomologyRings.Eliminator-Poly-Quotient-to-Ring

open import Cubical.Data.Unit
open import Cubical.HITs.Sn
open import Cubical.ZCohomology.Groups.Sn

private variable
  ℓ ℓ' : Level

open Iso

module Equiv-Sn-Properties (n : ℕ) where

  open IsGroupHom

-----------------------------------------------------------------------------
-- Definitions

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

  open RingStr (snd (H*R (S₊ (suc n)))) using ()
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
-- Partition of ℕ

  data partℕ (k : ℕ) : Type ℓ-zero where
    is0         : (k ≡ 0)                      → partℕ k
    isInBetween : (k ≡ 0 → ⊥) × (k < (suc n)) → partℕ k
    isEq        : (k ≡ 0 → ⊥) × (k ≡ (suc n)) → partℕ k
    isAbove     : (k ≡ 0 → ⊥) × ((suc n) < k) → partℕ k

  postulate
    isPropPartℕ : (k : ℕ) → isProp (partℕ k)

  part : (k : ℕ) → partℕ k
  part k with (discreteℕ k 0)
  ... | yes p = is0 p
  ... | no ¬p with (k ≟ (suc n))
  ...         | lt x = isInBetween (¬p , x)
  ...         | eq x = isEq (¬p , x)
  ...         | gt x = isAbove (¬p , x)

  _part+_ : {k l : ℕ} → (xk : partℕ k) → (xl : partℕ l) → partℕ (k +n l)
  _part+_ {k} {l} xk xl = {!!}

  eq-part-part+ : (k l : ℕ) → part (k +n l) ≡ (part k) part+ (part l)
  eq-part-part+ k l = isPropPartℕ (k +n l) _ _ 




-----------------------------------------------------------------------------
-- As we are in the general case, the definition are now up to a path and not definitional
-- Hence when need to add transport to go from coHom 0 X to coHom 0 X
-- This some notation and usefull lemma

  SubstCoHom : {k l : ℕ} → (x : k ≡ l) → (a : coHom k (S₊ (suc n))) → coHom l (S₊ (suc n))
  SubstCoHom x a = subst (λ X → coHom X (S₊ (suc n))) x a

  -- solve a pbl of project with the notation
  SubstReflCoHom : {k : ℕ} → (a : coHom k (S₊ (suc n))) → subst (λ X → coHom X (S₊ (suc n))) refl a ≡ a
  SubstReflCoHom a = substRefl a

  subst-0 : (k l : ℕ) → (x : k ≡ l) → SubstCoHom x (0ₕ k) ≡ 0ₕ l
  subst-0 k l x = J (λ l x → SubstCoHom x (0ₕ k) ≡ 0ₕ l) (SubstReflCoHom (0ₕ k)) x

  subst-+ : (k : ℕ) → (a b : coHom k (S₊ (suc n))) → (l : ℕ) → (x : k ≡ l)
            → SubstCoHom x (a +ₕ b) ≡ SubstCoHom x a +ₕ SubstCoHom x b
  subst-+ k a b l x = J (λ l x → SubstCoHom x (a +ₕ b) ≡ SubstCoHom x a +ₕ SubstCoHom x b)
                        (SubstReflCoHom (a +ₕ b) ∙ sym (cong₂ _+ₕ_ (SubstReflCoHom a) (SubstReflCoHom b)))
                        x

  subst-⌣ : (k : ℕ) → (a b : coHom k (S₊ (suc n))) → (l : ℕ) → (x : k ≡ l)
            → SubstCoHom (cong₂ _+'_ x x) (a ⌣ b) ≡ SubstCoHom x a ⌣ SubstCoHom x b
  subst-⌣ k a b l x = J (λ l x → SubstCoHom (cong₂ _+'_ x x) (a ⌣ b) ≡ SubstCoHom x a ⌣ SubstCoHom x b)
                        (SubstReflCoHom (a ⌣ b) ∙ sym (cong₂ _⌣_ (SubstReflCoHom a) (SubstReflCoHom b)))
                        x



-----------------------------------------------------------------------------
-- Direct Sens on ℤ[x]

  base-trad-ℤ : (k : ℕ) → (a : ℤ) → (x : partℕ k) → H* (S₊ (suc n))
  base-trad-ℤ k a (is0 x)         = base 0 (inv (fst (H⁰-Sⁿ≅ℤ  n)) a)
  base-trad-ℤ k a (isInBetween x) = 0H*
  base-trad-ℤ k a (isEq x)        = base (suc n) (inv (fst (Hⁿ-Sⁿ≅ℤ n)) a)
  base-trad-ℤ k a (isAbove x)     = 0H*

  ℤ[x]→H*-Sⁿ : ℤ[x] → H* (S₊ (suc n))
  ℤ[x]→H*-Sⁿ = Poly-Rec-Set.f _ _ _ isSetH*
       0H*
       (λ { (k ∷ []) a → base-trad-ℤ k a (part k)})
       _+H*_
       +H*Assoc
       +H*Rid
       +H*Comm
       (λ { (k ∷ []) → base-neutral-eq k (part k)})
       λ { (k ∷ []) a b → base-add-eq k a b (part k)}
    where

    base-neutral-eq : (k : ℕ) → (x : partℕ k) → base-trad-ℤ k 0ℤ x ≡ 0H*
    base-neutral-eq k (is0 x)         = cong (base 0) (pres1 (snd (invGroupIso (H⁰-Sⁿ≅ℤ n)))) ∙ base-neutral _
    base-neutral-eq k (isInBetween x) = refl
    base-neutral-eq k (isEq x)        = cong (base (suc n)) (pres1 (snd (invGroupIso (Hⁿ-Sⁿ≅ℤ n)))) ∙ base-neutral _
    base-neutral-eq k (isAbove x)     = refl

    base-add-eq : (k : ℕ) → (a b : ℤ) → (x : partℕ k)
                  → base-trad-ℤ k a x +H* base-trad-ℤ k b x ≡ base-trad-ℤ k (a +ℤ b) x
    base-add-eq k a b (is0 x)         = base-add _ _ _ ∙ cong (base 0) (sym (pres· (snd (invGroupIso (H⁰-Sⁿ≅ℤ n))) a b))
    base-add-eq k a b (isInBetween x) = +H*Rid _
    base-add-eq k a b (isEq x)        = base-add _ _ _ ∙ cong (base (suc n)) (sym (pres· (snd (invGroupIso (Hⁿ-Sⁿ≅ℤ n))) a b))
    base-add-eq k a b (isAbove x)     = +H*Rid _

-----------------------------------------------------------------------------
-- Morphism on ℤ[x]

  -- doesn't compute without an abstract value !
  -- ℤ[x]→H*-Sⁿ-map1 : ℤ[x]→H*-Sⁿ (1Pℤ) ≡ 1H*
  -- ℤ[x]→H*-Sⁿ-map1 = cong (base 0) {!!}

  ℤ[x]→H*-Sⁿ-map+ : (x y : ℤ[x]) → ℤ[x]→H*-Sⁿ (x +Pℤ y) ≡ ℤ[x]→H*-Sⁿ x +H* ℤ[x]→H*-Sⁿ y
  ℤ[x]→H*-Sⁿ-map+ x y = refl

-- cup product on H⁰ → H⁰ → H⁰
  -- T0 : (z : ℤ) → coHom 0 (S₊ (suc n))
  -- T0 = inv (fst (H⁰-Sⁿ≅ℤ n))

  -- T0g : IsGroupHom (snd ℤG) T0 (coHomGr 0 (S₊ (suc n)) .snd)
  -- T0g = snd (invGroupIso (H⁰-Sⁿ≅ℤ n))

--   -- idea : control of the unfolding + simplification of T0 on the left
--   rmorph-base-case-00 : (a : ℤ) → (b : ℤ) →
--                         T0 (a ·ℤ b) ≡ (T0 a) ⌣ (T0 b)
--   rmorph-base-case-00 (pos zero)       b = (IsGroupHom.pres1 T0g)
--   rmorph-base-case-00 (pos (suc n))    b = ((IsGroupHom.pres· T0g b (pos n ·ℤ b)))
--                                            ∙ (cong (λ X → (T0 b) +ₕ X) (rmorph-base-case-00 (pos n) b))
--   rmorph-base-case-00 (negsuc zero)    b = cong T0 (sym (+ℤLid (-ℤ b))) -- issue with the definition of ℤCommRing and ℤGroup
--                                            ∙ IsGroupHom.presinv T0g b

--   rmorph-base-case-00 (negsuc (suc n)) b = cong T0 (+ℤComm (-ℤ b) (negsuc n ·ℤ b)) -- ·ℤ and ·₀ are defined asymetrically !
--                                            ∙ IsGroupHom.pres· T0g (negsuc n ·ℤ b) (-ℤ b)
--                                             ∙ cong₂ _+ₕ_ (rmorph-base-case-00 (negsuc n) b)
--                                                          (cong T0 (sym (+ℤLid (-ℤ b))) ∙ IsGroupHom.presinv T0g b)
-- -- cup product on H⁰ → Hⁿ → Hⁿ
--   T1 : (z : ℤ) → coHom 1 (S₊ 1)
--   T1 = λ z → inv (fst (Hᵐ-Sⁿ 1 1)) z

--   -- idea : control of the unfolding + simplification of T0 on the left
--   T1g : IsGroupHom (Cubical.Algebra.Group.ℤ .snd) (fst (invGroupIso (Hᵐ-Sⁿ 1 1)) .fun) (coHomGr 1 (S₊ 1) .snd)
--   T1g = snd (invGroupIso (Hᵐ-Sⁿ 1 1))

--   rmorph-base-case-01 : (a : ℤ) → (b : ℤ) →
--                         T1 (a ·ℤ b) ≡ (T0 a) ⌣ (T1 b)
--   rmorph-base-case-01 (pos zero)       b = (IsGroupHom.pres1 T1g)
--   rmorph-base-case-01 (pos (suc n))    b = ((IsGroupHom.pres· T1g b (pos n ·ℤ b)))
--                                            ∙ (cong (λ X → (T1 b) +ₕ X) (rmorph-base-case-01 (pos n) b))
--   rmorph-base-case-01 (negsuc zero)    b = cong T1 (sym (+ℤLid (-ℤ b))) -- issue with the definition of ℤCommRing and ℤGroup
--                                            ∙ IsGroupHom.presinv T1g b

--   rmorph-base-case-01 (negsuc (suc n)) b = cong T1 (+ℤComm (-ℤ b) (negsuc n ·ℤ b)) -- ·ℤ and ·₀ are defined asymetrically !
--                                            ∙ IsGroupHom.pres· T1g (negsuc n ·ℤ b) (-ℤ b)
--                                             ∙ cong₂ _+ₕ_ (rmorph-base-case-01 (negsuc n) b)
--                                                          (cong T1 (sym (+ℤLid (-ℤ b))) ∙ IsGroupHom.presinv T1g b)


-- Nice packaging of the proof
  -- basically just have to do 0 0 / 0 (S n)
  -- => have good computation rule for part+
  rmorph-base-case-part : (k : ℕ) → (a : ℤ) → (xk : partℕ k) →
                          (l : ℕ) → (b : ℤ) → (xl : partℕ l) →
                           base-trad-ℤ (k +n l) (a ·ℤ b) (xk part+ xl)
                              ≡ base-trad-ℤ k a xk cup base-trad-ℤ l b xl
  rmorph-base-case-part k a (is0 xk) l b (is0 xl)         = {!todo!}
  rmorph-base-case-part k a (is0 xk) l b (isInBetween xl) = {!inBetween => Unit!}
  rmorph-base-case-part k a (is0 xk) l b (isEq xl)        = {!todo!}
  rmorph-base-case-part k a (is0 xk) l b (isAbove xl)     = {!Above => Unit!}
  rmorph-base-case-part k a (isInBetween xk) l b (is0 xl)         = {!inBetween => Unit!}
  rmorph-base-case-part k a (isInBetween xk) l b (isInBetween xl) with ((k +n l) ≟ (suc n))
  ... | lt x = {!InBetween => Unit!}
  ... | eq x = {!IMPOSSIBLE!}
        -- Is is even possible ???
        -- Or do it in the other sens and get it automatically because 0 < k < S n => coHom k (S₊ (suc n)) ≅ UnitG
  ... | gt x = {!above => Unit!}
  rmorph-base-case-part k a (isInBetween xk) l b (isEq xl)        = {!above => Unit!}
  rmorph-base-case-part k a (isInBetween xk) l b (isAbove xl)     = {!above => Unit!}
  rmorph-base-case-part k a (isEq xk) l b (is0 x)         = {!gradedComm + case 0 k!}
  rmorph-base-case-part k a (isEq xk) l b (isInBetween x) = {!above => Unit!}
  rmorph-base-case-part k a (isEq xk) l b (isEq x)        = {!above => Unit!}
  rmorph-base-case-part k a (isEq xk) l b (isAbove x)     = {!above => Unit!}
  rmorph-base-case-part k a (isAbove xk) l b xl = {!above => Unit!}



  rmorph-base-case-int : (k : ℕ) → (a : ℤ) → (l : ℕ) → (b : ℤ) →
                         -- ℤ[x]→H*-Sⁿ (baseP (k ∷ []) a ·Pℤ baseP (l ∷ []) b)
                         -- ≡ ℤ[x]→H*-Sⁿ (baseP (k ∷ []) a) cup ℤ[x]→H*-Sⁿ (baseP (l ∷ []) b)
                         base-trad-ℤ (k +n l) (a ·ℤ b) (part (k +n l))
                         ≡ (base-trad-ℤ k a (part k)) cup (base-trad-ℤ l b (part l))
                         -- need a coherence condition otherwise a match on xk xl won't do anything !
                         -- replacing part (k +n l) by an addition on part k / part l named part+
                         -- otherwise impossible to do in the general case 
  rmorph-base-case-int k a l b = cong (λ X → base-trad-ℤ (k +n l) (a ·ℤ b) X) (eq-part-part+ k l)
                                 ∙ rmorph-base-case-part k a (part k) l b (part l) 

  rmorph-base-case-vec : (v : Vec ℕ 1) → (a : ℤ) → (v' : Vec ℕ 1) → (b : ℤ) →
                ℤ[x]→H*-Sⁿ (baseP v a ·Pℤ baseP v' b)
              ≡ ℤ[x]→H*-Sⁿ (baseP v a) cup ℤ[x]→H*-Sⁿ (baseP v' b)
  rmorph-base-case-vec (k ∷ []) a (l ∷ []) b = rmorph-base-case-int k a l b

  -- proof of the morphism
  ℤ[x]→H*-Sⁿ-rmorph : (x y : ℤ[x]) → ℤ[x]→H*-Sⁿ (x ·Pℤ y) ≡ ℤ[x]→H*-Sⁿ x cup ℤ[x]→H*-Sⁿ y
  ℤ[x]→H*-Sⁿ-rmorph = Poly-Ind-Prop.f _ _ _
                         (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
                         (λ y → refl)
                         base-case
                         λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
    where
    base-case : _
    base-case (k ∷ []) a = Poly-Ind-Prop.f _ _ _ (λ _ → isSetH* _ _)
                           (sym (RingTheory.0RightAnnihilates (H*R (S₊ (suc n))) _))
                           (λ v' b → rmorph-base-case-vec (k ∷ []) a v' b)
                           λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*Rdist+ _ _ _)


-----------------------------------------------------------------------------
-- Function on ℤ[x]/x + morphism

  -- ℤ[x]→H*-Sⁿ-cancelX : (k : Fin 1) → ℤ[x]→H*-Sⁿ (<X²> k) ≡ 0H*
  -- ℤ[x]→H*-Sⁿ-cancelX zero = {!!}

--   ℤ[X]→H*-Sⁿ : RingHom (CommRing→Ring ℤ[X]) (H*R (S₊ 1))
--   fst ℤ[X]→H*-Sⁿ = ℤ[x]→H*-Sⁿ
--   snd ℤ[X]→H*-Sⁿ = makeIsRingHom ℤ[x]→H*-Sⁿ-map1Pℤ ℤ[x]→H*-Sⁿ-gmorph ℤ[x]→H*-Sⁿ-rmorph

--   ℤ[X]/X²→H*R-Sⁿ : RingHom (CommRing→Ring ℤ[X]/X²) (H*R (S₊ 1))
--   ℤ[X]/X²→H*R-Sⁿ = Rec-Quotient-FGIdeal-Ring.f ℤ[X] (H*R (S₊ 1)) ℤ[X]→H*-Sⁿ <X²> ℤ[x]→H*-Sⁿ-cancelX

--   ℤ[x]/x²→H*-Sⁿ : ℤ[x]/x² → H* (S₊ 1)
--   ℤ[x]/x²→H*-Sⁿ = fst ℤ[X]/X²→H*R-Sⁿ



-----------------------------------------------------------------------------
-- Converse Sens on ℤ[X] + ℤ[x]/x

  H*-Sⁿ→ℤ[x] : H* (S₊ (suc n)) → ℤ[x]
  H*-Sⁿ→ℤ[x] = DS-Rec-Set.f _ _ _ _ isSetPℤ
       0Pℤ
       (λ k a → base-trad k a (part k))
       _+Pℤ_
       +PℤAssoc
       +PℤRid
       +PℤComm
       (λ k → base-neutral-eq k (part k))
       λ k a b → base-add-eq k a b (part k)
    where
    base-trad : (k : ℕ) → (a : coHom k (S₊ (suc n))) (x : partℕ k) → ℤ[x]
    base-trad k a (is0 x)         = baseP (0 ∷ []) (fun (fst (H⁰-Sⁿ≅ℤ n)) (SubstCoHom x a))
    base-trad k a (isInBetween x) = 0Pℤ
    base-trad k a (isEq x)        = baseP ((suc n) ∷ []) (fun (fst (Hⁿ-Sⁿ≅ℤ n)) (SubstCoHom (snd x) a))
    base-trad k a (isAbove x)     = 0Pℤ


    base-neutral-eq : (k : ℕ) → (x : partℕ k) → base-trad k (0ₕ k) x ≡ 0Pℤ
    base-neutral-eq k (is0 x)         = cong (baseP (0 ∷ [])) (cong (fun (fst (H⁰-Sⁿ≅ℤ n))) (subst-0 k 0 x))
                                        ∙ cong (baseP (0 ∷ [])) (pres1 (snd (H⁰-Sⁿ≅ℤ n)))
                                        ∙ base-0P (0 ∷ [])
    base-neutral-eq k (isInBetween x) = refl
    base-neutral-eq k (isEq x)        = cong (baseP ((suc n) ∷ [])) (cong (fun (fst (Hⁿ-Sⁿ≅ℤ n))) (subst-0 k (suc n) (snd x)))
                                        ∙ cong (baseP ((suc n) ∷ [])) (pres1 (snd (Hⁿ-Sⁿ≅ℤ n)))
                                        ∙ base-0P ((suc n) ∷ [])
    base-neutral-eq k (isAbove x)     = refl


    base-add-eq : (k : ℕ) → (a b : coHom k (S₊ (suc n))) → (x : partℕ k)
                  → base-trad k a x +Pℤ base-trad k b x ≡ base-trad k (a +ₕ b) x
    base-add-eq k a b (is0 x)         = base-Poly+ _ _ _
                                        ∙ cong (baseP (0 ∷ [])) (sym (pres· (snd (H⁰-Sⁿ≅ℤ n)) _ _))
                                        ∙ cong (baseP (0 ∷ [])) (cong (fun (fst (H⁰-Sⁿ≅ℤ n))) (sym (subst-+ k a b 0 x)))
    base-add-eq k a b (isInBetween x) = +PℤRid _
    base-add-eq k a b (isEq x)        =  base-Poly+ _ _ _
                                        ∙ cong (baseP ((suc n) ∷ [])) (sym (pres· (snd (Hⁿ-Sⁿ≅ℤ n)) _ _))
                                        ∙ cong (baseP ((suc n) ∷ [])) (cong (fun (fst (Hⁿ-Sⁿ≅ℤ n))) (sym (subst-+ k a b (suc n) (snd x))))
    base-add-eq k a b (isAbove x)     = +PℤRid _


  H*-Sⁿ→ℤ[x]-gmorph : (x y : H* (S₊ (suc n))) → H*-Sⁿ→ℤ[x] ( x +H* y) ≡ H*-Sⁿ→ℤ[x] x +Pℤ H*-Sⁿ→ℤ[x] y
  H*-Sⁿ→ℤ[x]-gmorph x y = refl

  H*-Sⁿ→ℤ[x]/x² : H* (S₊ (suc n)) → ℤ[x]/x²
  H*-Sⁿ→ℤ[x]/x² = [_] ∘ H*-Sⁿ→ℤ[x]

  H*-Sⁿ→ℤ[x]/x²-gmorph : (x y : H* (S₊ (suc n))) → H*-Sⁿ→ℤ[x]/x² (x +H* y) ≡ (H*-Sⁿ→ℤ[x]/x² x) +PℤI (H*-Sⁿ→ℤ[x]/x² y)
  H*-Sⁿ→ℤ[x]/x²-gmorph x y = refl



-- -----------------------------------------------------------------------------
-- -- Section

--   e-sect : (x : H* (S₊ 1)) → ℤ[x]/x²→H*-Sⁿ (H*-Sⁿ→ℤ[x]/x² x) ≡ x
--   e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
--            refl
--            base-case
--            λ {U V} ind-U ind-V → cong₂ _+H*_ ind-U ind-V
--            where
--            base-case : _
--            base-case zero          a = cong (base 0) (leftInv (fst (Hᵐ-Sⁿ 0 1)) a)
--            base-case one           a = cong (base 1) (leftInv (fst (Hᵐ-Sⁿ 1 1)) a)
--            base-case (suc (suc n)) a = (sym (base-neutral (suc (suc n))))
--                                        ∙ cong (base (suc (suc n))) (isOfHLevelRetractFromIso 1 (fst (Hⁿ-Sᵐ≅0 (suc n) 0 nsnotz)) isPropUnit _ _)


-- -----------------------------------------------------------------------------
-- -- Retraction

--   e-retr : (x : ℤ[x]/x²) → H*-Sⁿ→ℤ[x]/x² (ℤ[x]/x²→H*-Sⁿ x) ≡ x
--   e-retr = elimProp-sq (λ _ → isSetPℤI _ _)
--            (Poly-Ind-Prop.f _ _ _ (λ _ → isSetPℤI _ _)
--            refl
--            base-case
--            λ {U V} ind-U ind-V → cong₂ _+PℤI_ ind-U ind-V)
--            where
--            base-case : _
--            base-case (zero ∷ [])        a = cong [_] (cong (baseP (0 ∷ [])) (rightInv (fst (Hᵐ-Sⁿ 0 1)) a))
--            base-case (one ∷ [])         a = cong [_] (cong (baseP (1 ∷ [])) (rightInv (fst (Hᵐ-Sⁿ 1 1)) a))
--            base-case (suc (suc n) ∷ []) a = eq/ 0Pℤ (baseP (suc (suc n) ∷ []) a) ∣ ((λ x → baseP (n ∷ []) (-ℤ a)) , helper) ∣₋₁
--              where
--              helper : _
--              helper = (+PℤLid _) ∙ cong₂ baseP (cong (λ X → X ∷ []) (sym (+-comm n 2))) (sym (·ℤRid _)) ∙ (sym (+PℤRid _))



-- -----------------------------------------------------------------------------
-- -- Computation of the Cohomology Ring

-- module _ where

--   open Equiv-S1-Properties

--   Sⁿ-CohomologyRing : RingEquiv (CommRing→Ring ℤ[X]/X²) (H*R (S₊ 1))
--   fst Sⁿ-CohomologyRing = isoToEquiv is
--     where
--     is : Iso ℤ[x]/x² (H* (S₊ 1))
--     fun is = ℤ[x]/x²→H*-Sⁿ
--     inv is = H*-Sⁿ→ℤ[x]/x²
--     rightInv is = e-sect
--     leftInv is = e-retr
--   snd Sⁿ-CohomologyRing = snd ℤ[X]/X²→H*R-Sⁿ

--   CohomologyRing-Sⁿ : RingEquiv (H*R (S₊ 1)) (CommRing→Ring ℤ[X]/X²)
--   CohomologyRing-Sⁿ = RingEquivs.invEquivRing Sⁿ-CohomologyRing
