{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.ZCohomology.CohomologyRings.RP2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; discreteℕ)
open import Cubical.Data.Int
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Vec
open import Cubical.Data.FinData

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Instances.Bool
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
open import Cubical.HITs.RPn.Base

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.CohomologyRing
open import Cubical.ZCohomology.Groups.RP2
open import Cubical.ZCohomology.CohomologyRings.CupProductProperties

open Iso

module Equiv-RP2-Properties
  (H⁴-RP²≅ℤ : GroupIso (coHomGr 4 RP²) UnitGroup₀)
  where

-----------------------------------------------------------------------------
-- Definitions and import

  <2X,X²> :  FinVec ℤ[x] 2
  <2X,X²> zero = base (1 ∷ []) 2
  <2X,X²> (suc x) = base (2 ∷ []) 1

  ℤ[X]/<2X,X²> : CommRing ℓ-zero
  ℤ[X]/<2X,X²> = PolyCommRing-Quotient ℤCR <2X,X²>

  ℤ[x]/<2x,x²> : Type ℓ-zero
  ℤ[x]/<2x,x²> = fst ℤ[X]/<2X,X²>

  open IsGroupHom
  open gradedRingProperties

  open GroupStr (snd BoolGroup) using ()
    renaming
    ( 1g        to 0gBool
    ; _·_       to _+Bool_
    ; inv       to -Bool_
    ; ·Assoc    to +BoolAssoc
    ; ·IdL      to +BoolIdL
    ; ·IdR      to +BoolIdR
    ; is-set    to isSetBool   )

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

  open RingStr (snd (H*R RP²)) using ()
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

  open CommRingStr (snd ℤ[X]/<2X,X²>) using ()
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


  e₀ = invGroupIso H⁰-RP²≅ℤ
  ϕ₀ = fun (fst e₀)
  ϕ₀str = snd e₀
  ϕ₀⁻¹ = inv (fst e₀)
  ϕ₀⁻¹str = snd (invGroupIso e₀)
  ϕ₀-sect = rightInv (fst e₀)
  ϕ₀-retr = leftInv (fst e₀)

  e₂ = invGroupIso H²-RP²≅Bool
  ϕ₂ = fun (fst e₂)
  ϕ₂str = snd e₂
  ϕ₂⁻¹ = inv (fst e₂)
  ϕ₂⁻¹str = snd (invGroupIso e₂)
  ϕ₂-sect = rightInv (fst e₂)
  ϕ₂-retr = leftInv (fst e₂)

  data partℕ (k : ℕ) : Type ℓ-zero where
    is0  : (k ≡ 0)            → partℕ k
    is2  : (k ≡ 2)            → partℕ k
    else : ((k ≡ 0 → ⊥)
           × (k ≡ 2 → ⊥))    → partℕ k

  part : (k : ℕ) → partℕ k
  part k with (discreteℕ k 0)
  ... | yes p = is0 p
  ... | no ¬p with (discreteℕ k 2)
  ... |       yes q = is2 q
  ... |       no ¬q = else (¬p , ¬q)

  part0 : part 0 ≡ is0 refl
  part0 = refl

  part2 : part 2 ≡ is2 refl
  part2 = refl

-----------------------------------------------------------------------------
-- Direct Sens on ℤ[x]

  -- We need to add a group morphism from ℤ to Bool

  ψ₂ : ℤ → Bool
  ψ₂ = isEven

  ψ₂str : IsGroupHom (snd ℤG) ψ₂ (snd BoolGroup)
  ψ₂str = {!!}

  ϕ₂∘ψ₂str : IsGroupHom (snd ℤG) (ϕ₂ ∘ ψ₂) (snd (coHomGr 2 RP²))
  ϕ₂∘ψ₂str = isGroupHomComp (ψ₂ , ψ₂str) (ϕ₂ , ϕ₂str)

  ℤ[x]→H*-RP² : ℤ[x] → H* RP²
  ℤ[x]→H*-RP² = DS-Rec-Set.f _ _ _ _ isSetH*
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
               ϕ (one ∷ [])         a = base 2 ((ϕ₂ ∘ ψ₂) a)
               ϕ (suc (suc n) ∷ []) a = 0H*

               base-neutral-eq :  _
               base-neutral-eq (zero ∷ [])        = cong (base 0) (pres1 ϕ₀str) ∙ base-neutral _
               base-neutral-eq (one ∷ [])         = cong (base 2) (cong ϕ₂ (pres1 ψ₂str) ∙ pres1 ϕ₂str) ∙ base-neutral _
               base-neutral-eq (suc (suc n) ∷ []) = refl

               base-add-eq : _
               base-add-eq (zero ∷ []) a b        = (base-add _ _ _) ∙ (cong (base 0) (sym (pres· ϕ₀str _ _)))
               base-add-eq (one ∷ []) a b         = base-add _ _ _
                                                    ∙ cong (base 2) (sym (cong ϕ₂ (pres· ψ₂str a b) ∙ pres· ϕ₂str (ψ₂ a) (ψ₂ b)))
               base-add-eq (suc (suc n) ∷ []) a b = +H*IdR _

-- -----------------------------------------------------------------------------
-- -- Morphism on ℤ[x]


  ϕ₀-pres1 : ϕ₀ 1 ≡ 1⌣
  ϕ₀-pres1 = refl

  ℤ[x]→H*-RP²-pres1Pℤ : ℤ[x]→H*-RP² (1Pℤ) ≡ 1H*
  ℤ[x]→H*-RP²-pres1Pℤ = refl

  ℤ[x]→H*-RP²-pres+ : (x y : ℤ[x]) → ℤ[x]→H*-RP² (x +Pℤ y) ≡ ℤ[x]→H*-RP² x +H* ℤ[x]→H*-RP² y
  ℤ[x]→H*-RP²-pres+ x y = refl

  ϕ₀-gen : (n : ℕ) → (f : coHom n RP²) → ϕ₀ (pos 1) ⌣ f ≡ f
  ϕ₀-gen n f = cong (λ X → X ⌣ f) ϕ₀-pres1 ∙ rUnit⌣ n f

  open pres⌣

  -- Nice packaging of the proof
  pres·-base-case-int : (n : ℕ) → (a : ℤ) → (m : ℕ) → (b : ℤ) →
                ℤ[x]→H*-RP² (base (n ∷ []) a ·Pℤ base (m ∷ []) b)
              ≡ ℤ[x]→H*-RP² (base (n ∷ []) a) cup ℤ[x]→H*-RP² (base (m ∷ []) b)
  pres·-base-case-int zero          a zero          b = cong (base 0) (ϕₙ⌣ϕₘ ϕ₀ ϕ₀str ϕ₀ ϕ₀str ϕ₀ ϕ₀str (ϕ₀-gen _ _) a b)
  pres·-base-case-int zero          a one           b = cong (base 2) (ϕₙ⌣ϕₘ ϕ₀ ϕ₀str (ϕ₂ ∘ ψ₂) ϕ₂∘ψ₂str (ϕ₂ ∘ ψ₂) ϕ₂∘ψ₂str (ϕ₀-gen _ _) a b)
  pres·-base-case-int zero          a (suc (suc m)) b = refl
  pres·-base-case-int one           a zero          b = cong ℤ[x]→H*-RP² (·PℤComm (base (1 ∷ []) a) (base (0 ∷ []) b))
                                                        ∙ pres·-base-case-int 0 b 1 a
                                                        ∙ gradCommRing RP² 0 2 _ _
  pres·-base-case-int one           a one           b = sym (base-neutral 4) ∙
                                                         cong (base 4) (isOfHLevelRetractFromIso 1 (fst H⁴-RP²≅ℤ) isPropUnit _ _)
  pres·-base-case-int one           a (suc (suc m)) b = refl
  pres·-base-case-int (suc (suc n)) a m             b = refl


  pres·-base-case-vec : (v : Vec ℕ 1) → (a : ℤ) → (v' : Vec ℕ 1) → (b : ℤ) →
                ℤ[x]→H*-RP² (base v a ·Pℤ base v' b)
              ≡ ℤ[x]→H*-RP² (base v a) cup ℤ[x]→H*-RP² (base v' b)
  pres·-base-case-vec (n ∷ []) a (m ∷ []) b = pres·-base-case-int n a m b

  -- proof of the morphism
  ℤ[x]→H*-RP²-pres· : (x y : ℤ[x]) → ℤ[x]→H*-RP² (x ·Pℤ y) ≡ ℤ[x]→H*-RP² x cup ℤ[x]→H*-RP² y
  ℤ[x]→H*-RP²-pres· = DS-Ind-Prop.f _ _ _ _
                         (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
                         (λ y → refl)
                         base-case
                         λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
    where
    base-case : _
    base-case (n ∷ []) a = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
                           (sym (RingTheory.0RightAnnihilates (H*R RP²) _))
                           (λ v' b → pres·-base-case-vec (n ∷ []) a v' b)
                           λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*DistR+ _ _ _)


-- -----------------------------------------------------------------------------
-- -- Function on ℤ[x]/x + morphism

--   ℤ[x]→H*-S¹-cancelX : (k : Fin 1) → ℤ[x]→H*-S¹ (<X²> k) ≡ 0H*
--   ℤ[x]→H*-S¹-cancelX zero = refl

--   ℤ[X]→H*-S¹ : RingHom (CommRing→Ring ℤ[X]) (H*R (S₊ 1))
--   fst ℤ[X]→H*-S¹ = ℤ[x]→H*-S¹
--   snd ℤ[X]→H*-S¹ = makeIsRingHom ℤ[x]→H*-S¹-pres1Pℤ ℤ[x]→H*-S¹-pres+ ℤ[x]→H*-S¹-pres·

--   ℤ[X]/X²→H*R-S¹ : RingHom (CommRing→Ring ℤ[X]/X²) (H*R (S₊ 1))
--   ℤ[X]/X²→H*R-S¹ =
--     Quotient-FGideal-CommRing-Ring.inducedHom ℤ[X] (H*R (S₊ 1)) ℤ[X]→H*-S¹ <X²> ℤ[x]→H*-S¹-cancelX

--   ℤ[x]/x²→H*-S¹ : ℤ[x]/x² → H* (S₊ 1)
--   ℤ[x]/x²→H*-S¹ = fst ℤ[X]/X²→H*R-S¹



-----------------------------------------------------------------------------
-- Converse Sens on ℤ[X] + ℤ[x]/x

  -- Because ϕ⁻¹ are not morphism on there own
  -- We need to define functions directly from H* to Z[X]/<2X, X³>

  ψ₂⁻¹ : Bool → ℤ
  ψ₂⁻¹ false = 1
  ψ₂⁻¹ true = 0

  ψ₂⁻¹∘ϕ₂⁻¹str : IsGroupHom (snd (coHomGr 2 RP²)) (ψ₂⁻¹ ∘ ϕ₂⁻¹) (snd ℤG)
  ψ₂⁻¹∘ϕ₂⁻¹str = {!!}

  H*-S¹→ℤ[x]/<2x,x²> : H* RP² → ℤ[x]/<2x,x²>
  H*-S¹→ℤ[x]/<2x,x²> = DS-Rec-Set.f _ _ _ _ isSetPℤI
                        0PℤI
                        (λ { k a → ϕ⁻¹ k a (part k)})
                        _+PℤI_
                        +PℤIAssoc
                        +PℤIIdR
                        +PℤIComm
                        (λ k → base-neutral-eq k (part k))
                        λ k a b → base-add-eq k a b (part k)
       where
       ϕ⁻¹ : (k : ℕ) → (a : coHom k RP²) → (x : partℕ k) → ℤ[x]/<2x,x²>
       ϕ⁻¹ k a (is0 x) = [ (base (0 ∷ []) (ϕ₀⁻¹ (substG x a))) ]
       ϕ⁻¹ k a (is2 x) = [ (base (1 ∷ []) ((ψ₂⁻¹ ∘ ϕ₂⁻¹) (substG x a))) ]
       ϕ⁻¹ k a (else x) = 0PℤI

       base-neutral-eq : (k : ℕ) → (x : partℕ k) → ϕ⁻¹ k (0ₕ k) x ≡ 0PℤI
       base-neutral-eq k (is0 x) = cong [_] (cong (base {AGP = λ _ → snd (Ring→AbGroup (CommRing→Ring ℤCR))} (0 ∷ []))
                                                  (cong ϕ₀⁻¹ (subst0g x) ∙ pres1 ϕ₀⁻¹str)
                                            ∙ (base-neutral _))
       base-neutral-eq k (is2 x) = cong [_] (cong (base {AGP = λ _ → snd (Ring→AbGroup (CommRing→Ring ℤCR))} (1 ∷ []))
                                                  (cong (ψ₂⁻¹ ∘ ϕ₂⁻¹) (subst0g x) ∙ pres1 ψ₂⁻¹∘ϕ₂⁻¹str)
                                            ∙ (base-neutral _))
       base-neutral-eq k (else x) = refl

       base-add-eq : (k : ℕ) → (a b : coHom k RP²) → (x : partℕ k) →
                     (ϕ⁻¹ k a x) +PℤI (ϕ⁻¹ k b x) ≡ ϕ⁻¹ k (a +ₕ b) x
       base-add-eq k a b (is0 x) = cong [_] (base-add _ _ _
                                            ∙ cong (base (0 ∷ [])) (sym (pres· ϕ₀⁻¹str _ _) ∙ cong ϕ₀⁻¹ (subst+ _ _ _)))
       base-add-eq k a b (is2 x) = cong [_] (base-add _ _ _
                                            ∙ cong (base (1 ∷ [])) (sym (pres· ψ₂⁻¹∘ϕ₂⁻¹str _ _) ∙ cong (ψ₂⁻¹ ∘ ϕ₂⁻¹) (subst+ _ _ _)))
       base-add-eq k a b (else x) = +PℤIIdR _

  H*-S¹→ℤ[x]/<2x,x²>-pres0 : H*-S¹→ℤ[x]/<2x,x²> 0H* ≡ 0PℤI
  H*-S¹→ℤ[x]/<2x,x²>-pres0 = refl

  H*-S¹→ℤ[x]/<2x,x²>-pres+ : (x y : H* RP²) → H*-S¹→ℤ[x]/<2x,x²> (x +H* y) ≡ (H*-S¹→ℤ[x]/<2x,x²> x) +PℤI (H*-S¹→ℤ[x]/<2x,x²> y)
  H*-S¹→ℤ[x]/<2x,x²>-pres+ x y = refl



-- -----------------------------------------------------------------------------
-- -- Section

--   e-sect : (x : H* (S₊ 1)) → ℤ[x]/x²→H*-S¹ (H*-S¹→ℤ[x]/x² x) ≡ x
--   e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
--            refl
--            base-case
--            λ {U V} ind-U ind-V → cong₂ _+H*_ ind-U ind-V
--            where
--            base-case : _
--            base-case zero          a = cong (base 0) (ϕ₀-sect _)
--            base-case one           a = cong (base 1) (ϕ₁-sect _)
--            base-case (suc (suc n)) a = (sym (base-neutral (suc (suc n))))
--                                        ∙ cong (base (suc (suc n)))
--                                             (isOfHLevelRetractFromIso 1 (fst (Hⁿ-Sᵐ≅0 (suc n) 0 nsnotz)) isPropUnit _ _)


-- -----------------------------------------------------------------------------
-- -- Retraction

--   e-retr : (x : ℤ[x]/x²) → H*-S¹→ℤ[x]/x² (ℤ[x]/x²→H*-S¹ x) ≡ x
--   e-retr = SQ.elimProp (λ _ → isSetPℤI _ _)
--            (DS-Ind-Prop.f _ _ _ _ (λ _ → isSetPℤI _ _)
--            refl
--            base-case
--            λ {U V} ind-U ind-V → cong₂ _+PℤI_ ind-U ind-V)
--            where
--            base-case : _
--            base-case (zero ∷ [])        a = cong [_] (cong (base (0 ∷ [])) (ϕ₀-retr _))
--            base-case (one ∷ [])         a = cong [_] (cong (base (1 ∷ [])) (ϕ₁-retr _))
--            base-case (suc (suc n) ∷ []) a = eq/ 0Pℤ (base (suc (suc n) ∷ []) a) ∣ ((λ x → base (n ∷ []) (-ℤ a)) , helper) ∣₁
--              where
--              helper : _
--              helper = (+PℤIdL _) ∙ cong₂ base (cong (λ X → X ∷ []) (sym (+-comm n 2))) (sym (·ℤIdR _)) ∙ (sym (+PℤIdR _))


-- -----------------------------------------------------------------------------
-- -- Computation of the Cohomology Ring

-- module _ where

--   open Equiv-S1-Properties

--   S¹-CohomologyRing : RingEquiv (CommRing→Ring ℤ[X]/X²) (H*R (S₊ 1))
--   fst S¹-CohomologyRing = isoToEquiv is
--     where
--     is : Iso ℤ[x]/x² (H* (S₊ 1))
--     fun is = ℤ[x]/x²→H*-S¹
--     inv is = H*-S¹→ℤ[x]/x²
--     rightInv is = e-sect
--     leftInv is = e-retr
--   snd S¹-CohomologyRing = snd ℤ[X]/X²→H*R-S¹

--   CohomologyRing-S¹ : RingEquiv (H*R (S₊ 1)) (CommRing→Ring ℤ[X]/X²)
--   CohomologyRing-S¹ = RingEquivs.invRingEquiv S¹-CohomologyRing
