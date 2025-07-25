{-# OPTIONS --lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.Unit where

{-
   This file computes the cohomology ring of the Unit type as ℤ[X]/⟨X⟩ and as ℤ.
   This file is simpler than Sn and CP2 because
   - There is only one non trivial cohomology group.
   - The isomorphism function of H⁰ is simpler so it
     makes some properties hold definitionally.

   Though the file is almost written like Sn excet some simplification.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
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
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤCommRing to ℤCR)
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.Quotient
open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly
open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly-notationZ
open import Cubical.Algebra.Polynomials.Multivariate.EquivCarac.A[X]X-A

open import Cubical.HITs.Truncation
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/sq_)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.CohomologyRing
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.CohomologyRings.CupProductProperties

open Iso

module Equiv-Unit-Properties where

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

  open RingStr (snd (H*R Unit)) using ()
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
    ; ·DistR+   to ·PℤDistR+
    ; is-set    to isSetPℤ     )

  open CommRingStr (snd ℤ[X]/X) using ()
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

  e₀ = invGroupIso H⁰-Unit≅ℤ
  ϕ₀ = fun (fst e₀)
  ϕ₀str = snd e₀
  ϕ₀⁻¹ = inv (fst e₀)
  ϕ₀⁻¹str = snd (invGroupIso e₀)
  ϕ₀-sect = rightInv (fst e₀)
  ϕ₀-retr = leftInv (fst e₀)


-----------------------------------------------------------------------------
-- Direct Sens on ℤ[x]

  ℤ[x]→H*-Unit : ℤ[x] → H* Unit
  ℤ[x]→H*-Unit = DS-Rec-Set.f _ _ _ _ isSetH*
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
               ϕ (zero ∷ []) a = base zero (ϕ₀ a)
               ϕ (suc n ∷ []) a = 0H*

               base-neutral-eq :  _
               base-neutral-eq (zero ∷ []) = base-neutral _
               base-neutral-eq (suc n ∷ []) = refl

               base-add-eq : _
               base-add-eq (zero ∷ []) a b = base-add _ _ _
               base-add-eq (suc n ∷ []) a b = +H*IdR _

  ℤ[x]→H*-Unit-pres1Pℤ : ℤ[x]→H*-Unit (1Pℤ) ≡ 1H*
  ℤ[x]→H*-Unit-pres1Pℤ = refl

  ℤ[x]→H*-Unit-pres+ : (x y : ℤ[x]) → ℤ[x]→H*-Unit (x +Pℤ y) ≡ ℤ[x]→H*-Unit x +H* ℤ[x]→H*-Unit y
  ℤ[x]→H*-Unit-pres+ x y = refl


-- Proving the morphism on the cup product

  open pres⌣

  pres·-base-case-int : (n : ℕ) → (a : ℤ) → (m : ℕ) → (b : ℤ) →
                ℤ[x]→H*-Unit (base (n ∷ []) a ·Pℤ base (m ∷ []) b)
              ≡ ℤ[x]→H*-Unit (base (n ∷ []) a) cup ℤ[x]→H*-Unit (base (m ∷ []) b)
  pres·-base-case-int zero    a zero    b = cong (base 0) (ϕₙ⌣ϕₘ ϕ₀ ϕ₀str ϕ₀ ϕ₀str ϕ₀ ϕ₀str refl a b)
  pres·-base-case-int zero    a (suc m) b = refl
  pres·-base-case-int (suc n) a m       b = refl

  pres·-base-case-vec : (v : Vec ℕ 1) → (a : ℤ) → (v' : Vec ℕ 1) → (b : ℤ) →
                ℤ[x]→H*-Unit (base v a ·Pℤ base v' b)
              ≡ ℤ[x]→H*-Unit (base v a) cup ℤ[x]→H*-Unit (base v' b)
  pres·-base-case-vec (n ∷ []) a (m ∷ []) b = pres·-base-case-int n a m b


  ℤ[x]→H*-Unit-pres· : (x y : ℤ[x]) → ℤ[x]→H*-Unit (x ·Pℤ y) ≡ ℤ[x]→H*-Unit x cup ℤ[x]→H*-Unit y
  ℤ[x]→H*-Unit-pres· = DS-Ind-Prop.f _ _ _ _
                         (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
                         (λ y → refl)
                         base-case
                         λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
    where
    base-case : _
    base-case (n ∷ []) a = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
                           (sym (RingTheory.0RightAnnihilates (H*R Unit) _))
                           (λ v' b → pres·-base-case-vec (n ∷ []) a v' b)
                           λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*DistR+ _ _ _)


  -- raising to the product
  ℤ[x]→H*-Unit-cancelX : (k : Fin 1) → ℤ[x]→H*-Unit (<X> k) ≡ 0H*
  ℤ[x]→H*-Unit-cancelX zero = refl

  ℤ[X]→H*-Unit : RingHom (CommRing→Ring ℤ[X]) (H*R Unit)
  fst ℤ[X]→H*-Unit = ℤ[x]→H*-Unit
  snd ℤ[X]→H*-Unit = makeIsRingHom ℤ[x]→H*-Unit-pres1Pℤ ℤ[x]→H*-Unit-pres+ ℤ[x]→H*-Unit-pres·

  ℤ[X]/X→H*R-Unit : RingHom (CommRing→Ring ℤ[X]/X) (H*R Unit)
  ℤ[X]/X→H*R-Unit = Quotient-FGideal-CommRing-Ring.inducedHom ℤ[X] (H*R Unit) ℤ[X]→H*-Unit <X> ℤ[x]→H*-Unit-cancelX

  ℤ[x]/x→H*-Unit : ℤ[x]/x → H* Unit
  ℤ[x]/x→H*-Unit = fst ℤ[X]/X→H*R-Unit



-----------------------------------------------------------------------------
-- Converse Sens on ℤ[X]

  H*-Unit→ℤ[x] : H* Unit → ℤ[x]
  H*-Unit→ℤ[x] = DS-Rec-Set.f _ _ _ _ isSetPℤ
                  0Pℤ
                  ϕ⁻¹
                  _+Pℤ_
                  +PℤAssoc
                  +PℤIdR
                  +PℤComm
                  base-neutral-eq
                  base-add-eq
               where
               ϕ⁻¹ : (n : ℕ) → coHom n Unit → ℤ[x]
               ϕ⁻¹ zero a = base (0 ∷ []) (ϕ₀⁻¹ a)
               ϕ⁻¹ (suc n) a = 0Pℤ

               base-neutral-eq : _
               base-neutral-eq zero = base-neutral _
               base-neutral-eq (suc n) = refl

               base-add-eq : _
               base-add-eq zero a b = base-add _ _ _
                                      ∙ cong (base (0 ∷ [])) (sym (IsGroupHom.pres· ϕ₀⁻¹str a b))
               base-add-eq (suc n) a b = +PℤIdR _


  H*-Unit→ℤ[x]-pres+ : (x y : H* Unit) → H*-Unit→ℤ[x] (x +H* y) ≡ H*-Unit→ℤ[x] x +Pℤ H*-Unit→ℤ[x] y
  H*-Unit→ℤ[x]-pres+ x y = refl

  H*-Unit→ℤ[x]/x : H* Unit → ℤ[x]/x
  H*-Unit→ℤ[x]/x = [_] ∘ H*-Unit→ℤ[x]

  H*-Unit→ℤ[x]/x-pres+ : (x y : H* Unit) → H*-Unit→ℤ[x]/x (x +H* y) ≡ (H*-Unit→ℤ[x]/x x) +PℤI (H*-Unit→ℤ[x]/x y)
  H*-Unit→ℤ[x]/x-pres+ x y = cong [_] (H*-Unit→ℤ[x]-pres+ x y)



-----------------------------------------------------------------------------
-- Section

  e-sect : (x : H* Unit) → ℤ[x]/x→H*-Unit (H*-Unit→ℤ[x]/x x) ≡ x
  e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
           refl
           base-case
           λ {U V} ind-U ind-V → cong ℤ[x]/x→H*-Unit (H*-Unit→ℤ[x]/x-pres+ U V)
                                  ∙ IsRingHom.pres+ (snd ℤ[X]/X→H*R-Unit) (H*-Unit→ℤ[x]/x U) (H*-Unit→ℤ[x]/x V)
                                  ∙ cong₂ _+H*_ ind-U ind-V
           where
           base-case : _
           base-case zero a = cong (base 0) (ϕ₀-sect _)
           base-case (suc n) a = (sym (base-neutral (suc n)))
                                 ∙ (cong (base (suc n)) ((isContr→isProp (isContrHⁿ-Unit n) _ a)))


-----------------------------------------------------------------------------
-- Retraction

  e-retr : (x : ℤ[x]/x) → H*-Unit→ℤ[x]/x (ℤ[x]/x→H*-Unit x) ≡ x
  e-retr = SQ.elimProp (λ _ → isSetPℤI _ _)
           (DS-Ind-Prop.f _ _ _ _ (λ _ → isSetPℤI _ _)
           refl
           base-case
           λ {U V} ind-U ind-V → cong₂ _+PℤI_ ind-U ind-V)
           where
           base-case : _
           base-case (zero ∷ []) a = refl
           base-case (suc n ∷ []) a = eq/ 0Pℤ (base (suc n ∷ []) a) ∣ ((λ x → base (n ∷ []) (-ℤ a)) , foo) ∣₁
             where
             foo : (0Pℤ +Pℤ base (suc n ∷ []) (- a)) ≡ (base (n +n 1 ∷ []) (- a · pos 1) +Pℤ 0Pℤ)
             foo = (0Pℤ +Pℤ base (suc n ∷ []) (- a)) ≡⟨ +PℤIdL _ ⟩
                   base (suc n ∷ []) (- a) ≡⟨ cong₂ base (cong (λ X → X ∷ []) (sym ((+-suc n 0)
                                              ∙ (cong suc (+-zero n))))) (sym (·ℤIdR _)) ⟩
                   base (n +n suc 0 ∷ []) (- a ·ℤ 1ℤ) ≡⟨ refl ⟩
                   base (n +n 1 ∷ []) (- a · pos 1) ≡⟨ sym (+PℤIdR _) ⟩
                   (base (n +n 1 ∷ []) (- a · pos 1) +Pℤ 0Pℤ) ∎



-----------------------------------------------------------------------------
-- Computation of the Cohomology Ring

module _ where

  open Equiv-Unit-Properties
  open RingEquivs

  Unit-CohomologyRingP : RingEquiv (CommRing→Ring ℤ[X]/X) (H*R Unit)
  fst Unit-CohomologyRingP = isoToEquiv is
    where
    is : Iso ℤ[x]/x (H* Unit)
    fun is = ℤ[x]/x→H*-Unit
    inv is = H*-Unit→ℤ[x]/x
    rightInv is = e-sect
    leftInv is = e-retr
  snd Unit-CohomologyRingP = snd ℤ[X]/X→H*R-Unit

  CohomologyRing-UnitP : RingEquiv (H*R Unit) (CommRing→Ring ℤ[X]/X)
  CohomologyRing-UnitP = invRingEquiv Unit-CohomologyRingP

  Unit-CohomologyRingℤ : RingEquiv (CommRing→Ring ℤCR) (H*R Unit)
  Unit-CohomologyRingℤ = compRingEquiv (invRingEquiv Equiv-ℤ[X]/X-ℤ) Unit-CohomologyRingP

  CohomologyRing-Unitℤ : RingEquiv (H*R Unit) (CommRing→Ring ℤCR)
  CohomologyRing-Unitℤ = compRingEquiv CohomologyRing-UnitP Equiv-ℤ[X]/X-ℤ
