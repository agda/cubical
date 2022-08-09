{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.Sn where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Nat renaming (_+_ to _+n_ ; +-comm to +n-comm ; _·_ to _·n_ ; snotz to nsnotz)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.FinData

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Instances.Int renaming (ℤGroup to ℤG)
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.QuotientRing
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤCommRing to ℤCR)
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-notationZ

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/sq_)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation
open import Cubical.HITs.Sn

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.CohomologyRing
open import Cubical.ZCohomology.Groups.Sn

open Iso
open PlusBis

-----------------------------------------------------------------------------
-- Somme properties over H⁰-Sⁿ≅ℤ
module Properties-H⁰-Sⁿ≅ℤ where

  open RingStr

  T0m : (m : ℕ) → (z : ℤ) → coHom 0 (S₊ (suc m))
  T0m m = inv (fst (H⁰-Sⁿ≅ℤ m))

  T0mg : (m : ℕ) → IsGroupHom (snd ℤG) (T0m m) (coHomGr 0 (S₊ (suc m)) .snd)
  T0mg m = snd (invGroupIso (H⁰-Sⁿ≅ℤ m))

  T0m-pres1 : (m : ℕ) → base 0 ((T0m m) 1) ≡ 1r (snd (H*R (S₊ (suc m))))
  T0m-pres1 zero = refl
  T0m-pres1 (suc m) = refl

  T0m-pos0 : (m : ℕ) → {l : ℕ} → (x : coHom l (S₊ (suc m))) → (T0m m) (pos zero) ⌣ x ≡ 0ₕ l
  T0m-pos0 zero = ST.elim (λ x  → isProp→isSet (squash₂ _ _)) λ x → refl
  T0m-pos0 (suc m) = ST.elim (λ x  → isProp→isSet (squash₂ _ _)) λ x → refl

  T0m-posS : (m : ℕ) → {l : ℕ} → (k : ℕ) → (x : coHom l (S₊ (suc m)))
            → T0m m (pos (suc k)) ⌣ x ≡ x +ₕ (T0m m (pos k) ⌣ x)
  T0m-posS zero k = ST.elim (λ x → isProp→isSet (squash₂ _ _)) (λ x → refl)
  T0m-posS (suc m) k = ST.elim (λ x → isProp→isSet (squash₂ _ _)) (λ x → refl)

  T0m-neg0 : (m : ℕ) → {l : ℕ} → (x : coHom l (S₊ (suc m))) → T0m m (negsuc zero) ⌣ x ≡ -ₕ x
  T0m-neg0 zero = ST.elim (λ x → isProp→isSet (squash₂ _ _)) (λ x → refl)
  T0m-neg0 (suc m) = ST.elim (λ x → isProp→isSet (squash₂ _ _)) (λ x → refl)

  T0m-negS : (m : ℕ) → {l : ℕ} → (k : ℕ) → (x : coHom l (S₊ (suc m)))
            → T0m m (negsuc (suc k)) ⌣ x ≡ (T0m m (negsuc k) ⌣ x) +ₕ (-ₕ x)
  T0m-negS zero k = ST.elim (λ x → isProp→isSet (squash₂ _ _)) (λ x → refl)
  T0m-negS (suc m) k = ST.elim (λ x → isProp→isSet (squash₂ _ _)) (λ x → refl)



-----------------------------------------------------------------------------
-- Definitions

module Equiv-Sn-Properties (n : ℕ) where

  open IsGroupHom
  open Properties-H⁰-Sⁿ≅ℤ
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

  open RingStr (snd (H*R (S₊ (suc n)))) using ()
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

-----------------------------------------------------------------------------
-- Partition of ℕ

  data partℕ (k : ℕ) : Type ℓ-zero where
    is0  : (k ≡ 0)                          → partℕ k
    isSn : (k ≡ suc n)                      → partℕ k
    else : (k ≡ 0 → ⊥) × (k ≡ suc n → ⊥) → partℕ k

  part : (k : ℕ) → partℕ k
  part k with (discreteℕ k 0)
  ... | yes p = is0 p
  ... | no ¬p with (discreteℕ k (suc n))
  ... |            yes q = isSn q
  ... |            no ¬q = else (¬p , ¬q)


  part0 : part 0 ≡ is0 refl
  part0 = refl

  partSn : (x : partℕ (suc n)) → x ≡ isSn refl
  partSn (is0 x)  = ⊥.rec (nsnotz x)
  partSn (isSn x) = cong isSn (isSetℕ _ _ _ _)
  partSn (else x) = ⊥.rec (snd x refl)



-----------------------------------------------------------------------------
-- As we are in the general case, the definition are now up to a path and not definitional
-- Hence when need to add transport to go from coHom 0 X to coHom 0 X
-- This some notation and usefull lemma

  substCoHom : {k l : ℕ} → (x : k ≡ l) → (a : coHom k (S₊ (suc n))) → coHom l (S₊ (suc n))
  substCoHom x a = subst (λ X → coHom X (S₊ (suc n))) x a

  -- solve a pbl of project with the notation
  substReflCoHom : {k : ℕ} → (a : coHom k (S₊ (suc n))) → subst (λ X → coHom X (S₊ (suc n))) refl a ≡ a
  substReflCoHom a = substRefl a

  subst-0 : (k l : ℕ) → (x : k ≡ l) → substCoHom x (0ₕ k) ≡ 0ₕ l
  subst-0 k l x = J (λ l x → substCoHom x (0ₕ k) ≡ 0ₕ l) (substReflCoHom (0ₕ k)) x

  subst-+ : (k : ℕ) → (a b : coHom k (S₊ (suc n))) → (l : ℕ) → (x : k ≡ l)
            → substCoHom x (a +ₕ b) ≡ substCoHom x a +ₕ substCoHom x b
  subst-+ k a b l x = J (λ l x → substCoHom x (a +ₕ b) ≡ substCoHom x a +ₕ substCoHom x b)
                        (substReflCoHom (a +ₕ b) ∙ sym (cong₂ _+ₕ_ (substReflCoHom a) (substReflCoHom b)))
                        x

  subst-⌣ : (k : ℕ) → (a b : coHom k (S₊ (suc n))) → (l : ℕ) → (x : k ≡ l)
            → substCoHom (cong₂ _+'_ x x) (a ⌣ b) ≡ substCoHom x a ⌣ substCoHom x b
  subst-⌣ k a b l x = J (λ l x → substCoHom (cong₂ _+'_ x x) (a ⌣ b) ≡ substCoHom x a ⌣ substCoHom x b)
                        (substReflCoHom (a ⌣ b) ∙ sym (cong₂ _⌣_ (substReflCoHom a) (substReflCoHom b)))
                        x



-----------------------------------------------------------------------------
-- Direct Sens on ℤ[x]

  ℤ[x]→H*-Sⁿ : ℤ[x] → H* (S₊ (suc n))
  ℤ[x]→H*-Sⁿ = DS-Rec-Set.f _ _ _ _ isSetH*
       0H*
       base-trad
       _+H*_
       +H*Assoc
       +H*IdR
       +H*Comm
       base-neutral-eq
       base-add-eq
    where

    base-trad : _
    base-trad (zero ∷ []) a = base 0 (inv (fst (H⁰-Sⁿ≅ℤ n)) a)
    base-trad (one ∷ []) a = base (suc n) (inv (fst (Hⁿ-Sⁿ≅ℤ n)) a)
    base-trad (suc (suc k) ∷ []) a = 0H*

    base-neutral-eq : _
    base-neutral-eq (zero ∷ []) = cong (base 0) (pres1 (snd (invGroupIso (H⁰-Sⁿ≅ℤ n)))) ∙ base-neutral _
    base-neutral-eq (one ∷ []) = cong (base (suc n)) (pres1 (snd (invGroupIso (Hⁿ-Sⁿ≅ℤ n)))) ∙ base-neutral _
    base-neutral-eq (suc (suc k) ∷ []) = refl

    base-add-eq : _
    base-add-eq (zero ∷ []) a b = base-add _ _ _ ∙ cong (base 0) (sym (pres· (snd (invGroupIso (H⁰-Sⁿ≅ℤ n))) a b))
    base-add-eq (one ∷ []) a b = base-add _ _ _ ∙ cong (base (suc n)) (sym (pres· (snd (invGroupIso (Hⁿ-Sⁿ≅ℤ n))) a b))
    base-add-eq (suc (suc k) ∷ []) a b = +H*IdR _


-----------------------------------------------------------------------------
-- Morphism on ℤ[x]

  -- doesn't compute without an abstract value !
  ℤ[x]→H*-Sⁿ-pres1 : ℤ[x]→H*-Sⁿ (1Pℤ) ≡ 1H*
  ℤ[x]→H*-Sⁿ-pres1 = T0m-pres1 n

  ℤ[x]→H*-Sⁿ-pres+ : (x y : ℤ[x]) → ℤ[x]→H*-Sⁿ (x +Pℤ y) ≡ ℤ[x]→H*-Sⁿ x +H* ℤ[x]→H*-Sⁿ y
  ℤ[x]→H*-Sⁿ-pres+ x y = refl

  T0 = T0m n
  T0g = T0mg n
  T0-pos0 = T0m-pos0 n
  T0-posS = T0m-posS n
  T0-neg0 = T0m-neg0 n
  T0-negS = T0m-negS n

-- cup product on H⁰ → Hⁿ → Hⁿ
  module _
    (l : ℕ)
    (Tl : (z : ℤ) → coHom l (S₊ (suc n)))
    (Tlg : IsGroupHom (ℤG .snd) Tl (coHomGr l (S₊ (suc n)) .snd))
    where

      pres·-base-case-0l : (a : ℤ) → (b : ℤ) →
                            Tl (a ·ℤ b) ≡ (T0 a) ⌣ (Tl b)
      pres·-base-case-0l (pos zero)       b = pres1 Tlg
                                               ∙ sym (T0-pos0 (Tl b))
      pres·-base-case-0l (pos (suc k))    b = pres· Tlg b (pos k ·ℤ b)
                                               ∙ cong (λ X → (Tl b) +ₕ X) (pres·-base-case-0l (pos k) b)
                                               ∙ sym (T0-posS k (Tl b))
      pres·-base-case-0l (negsuc zero)    b =  presinv Tlg b
                                               ∙ sym (T0-neg0 (Tl b))
      pres·-base-case-0l (negsuc (suc k)) b = cong Tl (+ℤComm (-ℤ b) (negsuc k ·ℤ b))
                                               ∙ pres· Tlg (negsuc k ·ℤ b) (-ℤ b)
                                               ∙ cong₂ _+ₕ_ (pres·-base-case-0l (negsuc k) b)
                                                            (presinv Tlg b)
                                               ∙ sym (T0-negS k (Tl b))


-- Nice packging of the proof
  pres·-base-case-int : (k : ℕ) → (a : ℤ) → (l : ℕ) → (b : ℤ) →
                         ℤ[x]→H*-Sⁿ (base (k ∷ []) a ·Pℤ base (l ∷ []) b)
                         ≡ ℤ[x]→H*-Sⁿ (base (k ∷ []) a) cup ℤ[x]→H*-Sⁿ (base (l ∷ []) b)
  pres·-base-case-int zero          a zero          b = cong (base 0) (pres·-base-case-0l 0 (inv (fst (H⁰-Sⁿ≅ℤ n)))
                                                                                              (snd (invGroupIso (H⁰-Sⁿ≅ℤ n))) a b)
  pres·-base-case-int zero          a one           b = cong (base (suc n)) (pres·-base-case-0l (suc n) (inv (fst (Hⁿ-Sⁿ≅ℤ n)))
                                                                                                  (snd (invGroupIso (Hⁿ-Sⁿ≅ℤ n))) a b)
  pres·-base-case-int zero          a (suc (suc l)) b = refl
  pres·-base-case-int one           a zero          b = cong ℤ[x]→H*-Sⁿ (·PℤComm (base (one ∷ []) a) (base (zero ∷ []) b))
                                                         ∙ pres·-base-case-int zero b one a
                                                         ∙ gradCommRing (S₊ (suc n)) 0 (suc n) (inv (fst (H⁰-Sⁿ≅ℤ n)) b) (inv (fst (Hⁿ-Sⁿ≅ℤ n)) a)
  pres·-base-case-int one           a one           b = sym (base-neutral (suc n +' suc n))
                                                         ∙ cong (base (suc n +' suc n))
                                                           (isOfHLevelRetractFromIso
                                                                1
                                                                (fst (Hⁿ-Sᵐ≅0 (suc (n +n n)) n (λ p → <→≢ (n , (+n-comm n (suc n))) (sym p))))
                                                                isPropUnit _ _)
  pres·-base-case-int one           a (suc (suc l)) b = refl
  pres·-base-case-int (suc (suc k)) a             l b = refl





  pres·-base-case-vec : (v : Vec ℕ 1) → (a : ℤ) → (v' : Vec ℕ 1) → (b : ℤ) →
                ℤ[x]→H*-Sⁿ (base v a ·Pℤ base v' b)
              ≡ ℤ[x]→H*-Sⁿ (base v a) cup ℤ[x]→H*-Sⁿ (base v' b)
  pres·-base-case-vec (k ∷ []) a (l ∷ []) b = pres·-base-case-int k a l b

  -- proof of the morphism
  ℤ[x]→H*-Sⁿ-pres· : (x y : ℤ[x]) → ℤ[x]→H*-Sⁿ (x ·Pℤ y) ≡ ℤ[x]→H*-Sⁿ x cup ℤ[x]→H*-Sⁿ y
  ℤ[x]→H*-Sⁿ-pres· = DS-Ind-Prop.f _ _ _ _
                         (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
                         (λ y → refl)
                         base-case
                         λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
    where
    base-case : _
    base-case (k ∷ []) a = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
                           (sym (RingTheory.0RightAnnihilates (H*R (S₊ (suc n))) _))
                           (λ v' b → pres·-base-case-vec (k ∷ []) a v' b)
                           λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*DistR+ _ _ _)


-----------------------------------------------------------------------------
-- Function on ℤ[x]/x + morphism

  ℤ[x]→H*-Sⁿ-cancelX : (k : Fin 1) → ℤ[x]→H*-Sⁿ (<X²> k) ≡ 0H*
  ℤ[x]→H*-Sⁿ-cancelX zero = refl

  ℤ[X]→H*-Sⁿ : RingHom (CommRing→Ring ℤ[X]) (H*R (S₊ (suc n)))
  fst ℤ[X]→H*-Sⁿ = ℤ[x]→H*-Sⁿ
  snd ℤ[X]→H*-Sⁿ = makeIsRingHom ℤ[x]→H*-Sⁿ-pres1 ℤ[x]→H*-Sⁿ-pres+ ℤ[x]→H*-Sⁿ-pres·

  ℤ[X]/X²→H*R-Sⁿ : RingHom (CommRing→Ring ℤ[X]/X²) (H*R (S₊ (suc n)))
  ℤ[X]/X²→H*R-Sⁿ =
    Quotient-FGideal-CommRing-Ring.inducedHom ℤ[X] (H*R (S₊ (suc n))) ℤ[X]→H*-Sⁿ <X²> ℤ[x]→H*-Sⁿ-cancelX

  ℤ[x]/x²→H*-Sⁿ : ℤ[x]/x² → H* (S₊ (suc n))
  ℤ[x]/x²→H*-Sⁿ = fst ℤ[X]/X²→H*R-Sⁿ



-----------------------------------------------------------------------------
-- Converse Sens on ℤ[X] + ℤ[x]/x

  base-trad-H* : (k : ℕ) → (a : coHom k (S₊ (suc n))) → (x : partℕ k) → ℤ[x]
  base-trad-H* k a (is0 x) = base (0 ∷ []) (fun (fst (H⁰-Sⁿ≅ℤ n)) (substCoHom x a))
  base-trad-H* k a (isSn x) = base (1 ∷ []) (fun (fst (Hⁿ-Sⁿ≅ℤ n)) (substCoHom x a))
  base-trad-H* k a (else x) = 0Pℤ

  H*-Sⁿ→ℤ[x] : H* (S₊ (suc n)) → ℤ[x]
  H*-Sⁿ→ℤ[x] = DS-Rec-Set.f _ _ _ _ isSetPℤ
       0Pℤ
       (λ k a → base-trad-H* k a (part k))
       _+Pℤ_
       +PℤAssoc
       +PℤIdR
       +PℤComm
       (λ k → base-neutral-eq k (part k))
       λ k a b → base-add-eq k a b (part k)
    where

    base-neutral-eq : (k : ℕ) → (x : partℕ k) → base-trad-H* k (0ₕ k) x ≡ 0Pℤ
    base-neutral-eq k (is0 x)  = cong (base (0 ∷ [])) (cong (fun (fst (H⁰-Sⁿ≅ℤ n))) (subst-0 k 0 x))
                                 ∙ cong (base (0 ∷ [])) (pres1 (snd (H⁰-Sⁿ≅ℤ n)))
                                 ∙ base-neutral (0 ∷ [])
    base-neutral-eq k (isSn x) = cong (base (1 ∷ [])) (cong (fun (fst (Hⁿ-Sⁿ≅ℤ n))) (subst-0 k (suc n) x))
                                 ∙ cong (base (1 ∷ [])) (pres1 (snd (Hⁿ-Sⁿ≅ℤ n)))
                                 ∙ base-neutral (1 ∷ [])
    base-neutral-eq k (else x) = refl


    base-add-eq : (k : ℕ) → (a b : coHom k (S₊ (suc n))) → (x : partℕ k)
                  → base-trad-H* k a x +Pℤ base-trad-H* k b x ≡ base-trad-H* k (a +ₕ b) x
    base-add-eq k a b (is0 x) = base-add _ _ _
                                ∙ cong (base (0 ∷ [])) (sym (pres· (snd (H⁰-Sⁿ≅ℤ n)) _ _))
                                ∙ cong (base (0 ∷ [])) (cong (fun (fst (H⁰-Sⁿ≅ℤ n))) (sym (subst-+ k a b 0 x)))
    base-add-eq k a b (isSn x) =  base-add _ _ _
                                  ∙ cong (base (1 ∷ [])) (sym (pres· (snd (Hⁿ-Sⁿ≅ℤ n)) _ _))
                                  ∙ cong (base (1 ∷ [])) (cong (fun (fst (Hⁿ-Sⁿ≅ℤ n))) (sym (subst-+ k a b (suc n) x)))
    base-add-eq k a b (else x) = +PℤIdR _


  H*-Sⁿ→ℤ[x]-pres+ : (x y : H* (S₊ (suc n))) → H*-Sⁿ→ℤ[x] ( x +H* y) ≡ H*-Sⁿ→ℤ[x] x +Pℤ H*-Sⁿ→ℤ[x] y
  H*-Sⁿ→ℤ[x]-pres+ x y = refl

  H*-Sⁿ→ℤ[x]/x² : H* (S₊ (suc n)) → ℤ[x]/x²
  H*-Sⁿ→ℤ[x]/x² = [_] ∘ H*-Sⁿ→ℤ[x]

  H*-Sⁿ→ℤ[x]/x²-pres+ : (x y : H* (S₊ (suc n))) → H*-Sⁿ→ℤ[x]/x² (x +H* y) ≡ (H*-Sⁿ→ℤ[x]/x² x) +PℤI (H*-Sⁿ→ℤ[x]/x² y)
  H*-Sⁿ→ℤ[x]/x²-pres+ x y = refl



-----------------------------------------------------------------------------
-- Section

  e-sect-base : (k : ℕ) → (a : coHom k (S₊ (suc n))) → (x : partℕ k) →
                ℤ[x]/x²→H*-Sⁿ [ (base-trad-H* k a x) ] ≡ base k a
  e-sect-base k a (is0 x)  = cong (base 0) (leftInv (fst (H⁰-Sⁿ≅ℤ n)) (substCoHom x a))
                             ∙ sym (constSubstCommSlice (λ x → coHom x (S₊ (suc n))) (H* (S₊ (suc n))) base x a)

  e-sect-base k a (isSn x) = cong (base (suc n)) (leftInv (fst (Hⁿ-Sⁿ≅ℤ n)) (substCoHom x a))
                             ∙ sym (constSubstCommSlice (λ x → coHom x (S₊ (suc n))) (H* (S₊ (suc n))) base x a)
  e-sect-base k a (else x) = sym (base-neutral k)
                             ∙ constSubstCommSlice ((λ x → coHom x (S₊ (suc n)))) ((H* (S₊ (suc n)))) base (suc-predℕ k (fst x)) (0ₕ k)
                             ∙ cong (base (suc (predℕ k)))
                               ((isOfHLevelRetractFromIso 1
                                       (fst (Hⁿ-Sᵐ≅0 (predℕ k) n λ p → snd x (suc-predℕ k (fst x) ∙ cong suc p)))
                                       isPropUnit _ _))
                             ∙ sym (constSubstCommSlice ((λ x → coHom x (S₊ (suc n)))) ((H* (S₊ (suc n)))) base (suc-predℕ k (fst x)) a)

  e-sect : (x : H* (S₊ (suc n))) → ℤ[x]/x²→H*-Sⁿ (H*-Sⁿ→ℤ[x]/x² x) ≡ x
  e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
           refl
           (λ k a → e-sect-base k a (part k))
           λ {U V} ind-U ind-V → cong₂ _+H*_ ind-U ind-V


-----------------------------------------------------------------------------
-- Retraction

  e-retr : (x : ℤ[x]/x²) → H*-Sⁿ→ℤ[x]/x² (ℤ[x]/x²→H*-Sⁿ x) ≡ x
  e-retr = SQ.elimProp (λ _ → isSetPℤI _ _)
           (DS-Ind-Prop.f _ _ _ _ (λ _ → isSetPℤI _ _)
           refl
           base-case
           λ {U V} ind-U ind-V → cong₂ _+PℤI_ ind-U ind-V)
           where
           base-case : _
           base-case (zero ∷ []) a = cong [_] (cong (base-trad-H* 0 (inv (fst (H⁰-Sⁿ≅ℤ n)) a)) part0)
                                     ∙ cong [_] (cong (base (0 ∷ [])) (cong (fun (fst (H⁰-Sⁿ≅ℤ n)))
                                                                             (substReflCoHom (inv (fst (H⁰-Sⁿ≅ℤ n)) a))))
                                     ∙ cong [_] (cong (base (0 ∷ [])) (rightInv (fst (H⁰-Sⁿ≅ℤ n)) a))
           base-case (one ∷ []) a  = cong [_] (cong (base-trad-H* (suc n) (inv (fst (Hⁿ-Sⁿ≅ℤ n)) a)) (partSn (part (suc n))))
                                     ∙ cong [_] (cong (base (1 ∷ [])) (cong (fun (fst (Hⁿ-Sⁿ≅ℤ n)))
                                                                             (substReflCoHom (inv (fst (Hⁿ-Sⁿ≅ℤ n)) a))))
                                     ∙ cong [_] (cong (base (1 ∷ [])) (rightInv (fst (Hⁿ-Sⁿ≅ℤ n)) a))
           base-case (suc (suc k) ∷ []) a = eq/ 0Pℤ (base (suc (suc k) ∷ []) a)  ∣ ((λ x → base (k ∷ []) (-ℤ a)) , helper) ∣₁
             where
             helper : _
             helper = (+PℤIdL _) ∙ cong₂ base (cong (λ X → X ∷ []) (sym (+n-comm k 2))) (sym (·ℤIdR _)) ∙ (sym (+PℤIdR _))



-----------------------------------------------------------------------------
-- Computation of the Cohomology Ring

module _ (n : ℕ) where

  open Equiv-Sn-Properties n

  Sⁿ-CohomologyRing : RingEquiv (CommRing→Ring ℤ[X]/X²) (H*R (S₊ (suc n)))
  fst Sⁿ-CohomologyRing = isoToEquiv is
    where
    is : Iso ℤ[x]/x² (H* (S₊ (suc n)))
    fun is = ℤ[x]/x²→H*-Sⁿ
    inv is = H*-Sⁿ→ℤ[x]/x²
    rightInv is = e-sect
    leftInv is = e-retr
  snd Sⁿ-CohomologyRing = snd ℤ[X]/X²→H*R-Sⁿ

  CohomologyRing-Sⁿ : RingEquiv (H*R (S₊ (suc n))) (CommRing→Ring ℤ[X]/X²)
  CohomologyRing-Sⁿ = RingEquivs.invRingEquiv Sⁿ-CohomologyRing
