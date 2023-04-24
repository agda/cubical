{-# OPTIONS --safe --lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.Sn where

{-
   This file computes the cohomology ring of Sn (n ≥ 1)
   The big difference with Sn compared to S 1 is the fact that
   to do it for a general n, one needs to add a partition.
   This implies notably some transport operation that
   complicates the definition and the proofs.
-}

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
open import Cubical.Algebra.CommRing.Quotient
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
open import Cubical.ZCohomology.CohomologyRings.CupProductProperties

open Iso
open PlusBis

-----------------------------------------------------------------------------
-- Definitions

module Equiv-Sn-Properties (n : ℕ) where

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


  e₀ = invGroupIso (H⁰-Sⁿ≅ℤ n)
  ϕ₀ = fun (fst e₀)
  ϕ₀str = snd e₀
  ϕ₀⁻¹ = inv (fst e₀)
  ϕ₀⁻¹str = snd (invGroupIso e₀)
  ϕ₀-sect = rightInv (fst e₀)
  ϕ₀-retr = leftInv (fst e₀)

  eₙ = invGroupIso (Hⁿ-Sⁿ≅ℤ n)
  ϕₙ = fun (fst eₙ)
  ϕₙstr = snd eₙ
  ϕₙ⁻¹ = inv (fst eₙ)
  ϕₙ⁻¹str = snd (invGroupIso eₙ)
  ϕₙ-sect = rightInv (fst eₙ)
  ϕₙ-retr = leftInv (fst eₙ)

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
-- Direct Sens on ℤ[x]

  ℤ[x]→H*-Sⁿ : ℤ[x] → H* (S₊ (suc n))
  ℤ[x]→H*-Sⁿ = DS-Rec-Set.f _ _ _ _ isSetH*
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
    ϕ (zero ∷ []) a = base 0 (ϕ₀ a)
    ϕ (one ∷ []) a = base (suc n) (ϕₙ a)
    ϕ (suc (suc k) ∷ []) a = 0H*

    base-neutral-eq : _
    base-neutral-eq (zero ∷ []) = cong (base 0) (pres1 ϕ₀str) ∙ base-neutral _
    base-neutral-eq (one ∷ []) = cong (base (suc n)) (pres1 ϕₙstr) ∙ base-neutral _
    base-neutral-eq (suc (suc k) ∷ []) = refl

    base-add-eq : _
    base-add-eq (zero ∷ []) a b = base-add _ _ _ ∙ cong (base 0) (sym (pres· ϕ₀str a b))
    base-add-eq (one ∷ []) a b = base-add _ _ _ ∙ cong (base (suc n)) (sym (pres· ϕₙstr a b))
    base-add-eq (suc (suc k) ∷ []) a b = +H*IdR _


-----------------------------------------------------------------------------
-- Morphism on ℤ[x]

  ϕ₀-pres1 : (m : ℕ) → inv (fst (H⁰-Sⁿ≅ℤ m)) 1 ≡ 1⌣
  ϕ₀-pres1 zero = refl
  ϕ₀-pres1 (suc m) = refl

  -- doesn't compute without an abstract value !
  ℤ[x]→H*-Sⁿ-pres1 : ℤ[x]→H*-Sⁿ (1Pℤ) ≡ 1H*
  ℤ[x]→H*-Sⁿ-pres1 = cong (base 0) (ϕ₀-pres1 n)

  ℤ[x]→H*-Sⁿ-pres+ : (x y : ℤ[x]) → ℤ[x]→H*-Sⁿ (x +Pℤ y) ≡ ℤ[x]→H*-Sⁿ x +H* ℤ[x]→H*-Sⁿ y
  ℤ[x]→H*-Sⁿ-pres+ x y = refl

  ϕ₀-gen : (k : ℕ) → (f : coHom k (S₊ (suc n))) → ϕ₀ (pos 1) ⌣ f ≡ f
  ϕ₀-gen k f = cong (λ X → X ⌣ f) (ϕ₀-pres1 n) ∙ rUnit⌣ k f

  open pres⌣

-- Nice packging of the proof
  pres·-base-case-int : (k : ℕ) → (a : ℤ) → (l : ℕ) → (b : ℤ) →
                         ℤ[x]→H*-Sⁿ (base (k ∷ []) a ·Pℤ base (l ∷ []) b)
                         ≡ ℤ[x]→H*-Sⁿ (base (k ∷ []) a) cup ℤ[x]→H*-Sⁿ (base (l ∷ []) b)
  pres·-base-case-int zero          a zero          b = cong (base 0) (ϕₙ⌣ϕₘ ϕ₀ ϕ₀str ϕ₀ ϕ₀str ϕ₀ ϕ₀str (ϕ₀-gen _ _) a b)
  pres·-base-case-int zero          a one           b = cong (base (suc n)) (ϕₙ⌣ϕₘ ϕ₀ ϕ₀str ϕₙ ϕₙstr ϕₙ ϕₙstr (ϕ₀-gen _ _) a b)
  pres·-base-case-int zero          a (suc (suc l)) b = refl
  pres·-base-case-int one           a zero          b = cong ℤ[x]→H*-Sⁿ (·PℤComm (base (one ∷ []) a) (base (zero ∷ []) b))
                                                         ∙ pres·-base-case-int zero b one a
                                                         ∙ gradCommRing (S₊ (suc n)) 0 (suc n) _ _
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
  base-trad-H* k a (is0 x) = base (0 ∷ []) (ϕ₀⁻¹ (substG x a))
  base-trad-H* k a (isSn x) = base (1 ∷ []) (ϕₙ⁻¹ (substG x a))
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
    base-neutral-eq k (is0 x)  = cong (base (0 ∷ [])) (cong ϕ₀⁻¹ (substG0 x))
                                 ∙ cong (base (0 ∷ [])) (pres1 ϕ₀⁻¹str)
                                 ∙ base-neutral (0 ∷ [])
    base-neutral-eq k (isSn x) = cong (base (1 ∷ [])) (cong ϕₙ⁻¹ (substG0 x))
                                 ∙ cong (base (1 ∷ [])) (pres1 ϕₙ⁻¹str)
                                 ∙ base-neutral (1 ∷ [])
    base-neutral-eq k (else x) = refl


    base-add-eq : (k : ℕ) → (a b : coHom k (S₊ (suc n))) → (x : partℕ k)
                  → base-trad-H* k a x +Pℤ base-trad-H* k b x ≡ base-trad-H* k (a +ₕ b) x
    base-add-eq k a b (is0 x) = base-add _ _ _
                                ∙ cong (base (0 ∷ [])) (sym (pres· ϕ₀⁻¹str _ _))
                                ∙ cong (base (0 ∷ [])) (cong ϕ₀⁻¹ (substG+ a b x))
    base-add-eq k a b (isSn x) =  base-add _ _ _
                                  ∙ cong (base (1 ∷ [])) (sym (pres· ϕₙ⁻¹str _ _))
                                  ∙ cong (base (1 ∷ [])) (cong ϕₙ⁻¹ (substG+ a b x))
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
  e-sect-base k a (is0 x)  = cong (base 0) (ϕ₀-sect (substG x a))
                             ∙ sym (constSubstCommSlice (λ x → coHom x (S₊ (suc n))) (H* (S₊ (suc n))) base x a)

  e-sect-base k a (isSn x) = cong (base (suc n)) (ϕₙ-sect (substG x a))
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
           base-case (zero ∷ []) a = cong [_] (cong (base-trad-H* 0 (ϕ₀ a)) part0)
                                     ∙ cong [_] (cong (base (0 ∷ [])) (cong ϕ₀⁻¹ (transportRefl (ϕ₀ a))))
                                     ∙ cong [_] (cong (base (0 ∷ [])) (ϕ₀-retr a))
           base-case (one ∷ []) a  = cong [_] (cong (base-trad-H* (suc n) (ϕₙ a)) (partSn (part (suc n))))
                                     ∙ cong [_] (cong (base (1 ∷ [])) (cong ϕₙ⁻¹ (transportRefl (ϕₙ a))))
                                     ∙ cong [_] (cong (base (1 ∷ [])) (ϕₙ-retr a))
           base-case (suc (suc k) ∷ []) a = eq/ _ _  ∣ ((λ x → base (k ∷ []) (-ℤ a)) , helper) ∣₁
             where
             helper : _
             helper = (+PℤIdL _)
                      ∙ cong₂ base (cong (λ X → X ∷ [])
                                   (sym (+n-comm k 2))) (sym (·ℤIdR _))
                      ∙ (sym (+PℤIdR _))



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
