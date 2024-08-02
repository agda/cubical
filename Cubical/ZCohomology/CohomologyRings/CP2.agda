{-# OPTIONS --safe --lossy-unification #-}
module Cubical.ZCohomology.CohomologyRings.CP2 where

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
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.Quotient
open import Cubical.Algebra.Polynomials.Multivariate.Base
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
open import Cubical.ZCohomology.Groups.CP2
open import Cubical.ZCohomology.CohomologyRings.CupProductProperties

open Iso
open gradedRingProperties

module ComputeCP²Notation
  (e₀ : GroupIso ℤGroup (coHomGr 0 CP²))
  (e₂ : GroupIso ℤGroup (coHomGr 2 CP²))
  (e₄ : GroupIso ℤGroup (coHomGr 4 CP²))
  where

  open IsGroupHom
  -- open pres

-----------------------------------------------------------------------------
-- Begin Notation

  ---------------------------------------------------------------------------
  -- Import Notation

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

  open RingStr (snd (H*R CP²)) using ()
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

  open CommRingStr (snd ℤ[X]/X³) using ()
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


  ---------------------------------------------------------------------------
  -- Equiv Notation

  ϕ₀ : ℤ → coHom 0 CP²
  ϕ₀ = fun (fst e₀)
  ϕ₀str = snd e₀
  ϕ₂ : ℤ → coHom 2 CP²
  ϕ₂ = fun (fst e₂)
  ϕ₂str = snd e₂
  ϕ₄ : ℤ → coHom 4 CP²
  ϕ₄ = fun (fst e₄)
  ϕ₄str = snd e₄

  ϕ₀⁻¹ = inv (fst e₀)
  ϕ₀⁻¹str = snd (invGroupIso e₀)
  ϕ₂⁻¹ = inv (fst e₂)
  ϕ₂⁻¹str = snd (invGroupIso e₂)
  ϕ₄⁻¹ = inv (fst e₄)
  ϕ₄⁻¹str = snd (invGroupIso e₄)

  ϕ₀-sect = rightInv (fst e₀)
  ϕ₂-sect = rightInv (fst e₂)
  ϕ₄-sect = rightInv (fst e₄)

  ϕ₀-retr = leftInv (fst e₀)
  ϕ₂-retr = leftInv (fst e₂)
  ϕ₄-retr = leftInv (fst e₄)


-- End Notation
-----------------------------------------------------------------------------
-- Begin proof of the equivalence


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

  open pres⌣

  module ComputeCP²Function
    (ϕ₀-pres1 : ϕ₀ 1ℤ ≡ 1⌣)
    (ϕ₀-gen : (n : ℕ) → (a : coHom n CP²) → ϕ₀ (pos 1) ⌣ a ≡ a)
    (eq⌣224 : ϕ₂ (pos 1) ⌣ ϕ₂ (pos 1) ≡ ϕ₄ (pos 1))
    where


  -----------------------------------------------------------------------------
  -- Direct Sens on ℤ[x]/<X³>

    -- Function on ℤ[x]
    ℤ[x]→H*-CP² : ℤ[x] → H* CP²
    ℤ[x]→H*-CP² = DS-Rec-Set.f _ _ _ _ isSetH*
         0H*
         ϕ
         _+H*_
         +H*Assoc
         +H*IdR
         +H*Comm
         base-neutral-eq
         base-add-eq
      where
      ϕ : (v : Vec ℕ 1) → (a : ℤ) → H* CP²
      ϕ (zero ∷ []) a = base 0 (ϕ₀ a)
      ϕ (one ∷ []) a  = base 2 (ϕ₂ a)
      ϕ (two ∷ []) a  = base 4 (ϕ₄ a)
      ϕ (suc (suc (suc k)) ∷ []) a = 0H*

      base-neutral-eq : _
      base-neutral-eq (zero ∷ []) = cong (base 0) (pres1 ϕ₀str) ∙ base-neutral _
      base-neutral-eq (one ∷ [])  = cong (base 2) (pres1 ϕ₂str) ∙ base-neutral _
      base-neutral-eq (two ∷ [])  = cong (base 4) (pres1 ϕ₄str) ∙ base-neutral _
      base-neutral-eq (suc (suc (suc k)) ∷ []) = refl

      base-add-eq : _
      base-add-eq (zero ∷ []) a b = base-add _ _ _ ∙ cong (base 0) (sym (pres· ϕ₀str _ _))
      base-add-eq (one ∷ []) a b  = base-add _ _ _ ∙ cong (base 2) (sym (pres· ϕ₂str _ _))
      base-add-eq (two ∷ []) a b  = base-add _ _ _ ∙ cong (base 4) (sym (pres· ϕ₄str _ _))
      base-add-eq (suc (suc (suc k)) ∷ []) a b = +H*IdR _

    ℤ[x]→H*-CP²-pres1 : ℤ[x]→H*-CP² (1Pℤ) ≡ 1H*
    ℤ[x]→H*-CP²-pres1 = cong (base 0) ϕ₀-pres1

    ℤ[x]→H*-CP²-map+ : (x y : ℤ[x]) → ℤ[x]→H*-CP² (x +Pℤ y) ≡ ℤ[x]→H*-CP² x +H* ℤ[x]→H*-CP² y
    ℤ[x]→H*-CP²-map+ x y = refl


   -- Nice packaging of the cup product

    presCupInt : (k : ℕ) → (a : ℤ) → (l : ℕ) → (b : ℤ) →
                   ℤ[x]→H*-CP² (base (k ∷ []) a ·Pℤ base (l ∷ []) b)
                 ≡ ℤ[x]→H*-CP² (base (k ∷ []) a) cup ℤ[x]→H*-CP² (base (l ∷ []) b)
    presCupInt zero a zero b = cong (base 0) (ϕₙ⌣ϕₘ ϕ₀ ϕ₀str ϕ₀ ϕ₀str ϕ₀ ϕ₀str (ϕ₀-gen _ _) _ _)
    presCupInt zero a one b  = cong (base 2) ((ϕₙ⌣ϕₘ ϕ₀ ϕ₀str ϕ₂ ϕ₂str ϕ₂ ϕ₂str (ϕ₀-gen _ _) _ _))
    presCupInt zero a two b  = cong (base 4) ((ϕₙ⌣ϕₘ ϕ₀ ϕ₀str ϕ₄ ϕ₄str ϕ₄ ϕ₄str (ϕ₀-gen _ _) _ _))
    presCupInt zero a (suc (suc (suc l))) b = refl
    presCupInt one a zero b = cong ℤ[x]→H*-CP² (·PℤComm (base (one ∷ []) a) (base (zero ∷ []) b))
                              ∙ presCupInt zero b one a
                              ∙ gradCommRing CP² _ _ _ _
    presCupInt one a one b  = cong (base 4) ((ϕₙ⌣ϕₘ ϕ₂ ϕ₂str ϕ₂ ϕ₂str ϕ₄ ϕ₄str eq⌣224 _ _))
    presCupInt one a two b  = sym (base-neutral _)
                              ∙ cong (base 6) (unitGroupEq (Hⁿ-CP²≅0 _ (compute-eqℕ _ _) (compute-eqℕ _ _)) _ _)
    presCupInt one a (suc (suc (suc l))) b = refl
    presCupInt two a zero b = cong ℤ[x]→H*-CP² (·PℤComm (base (two ∷ []) a) (base (zero ∷ []) b))
                              ∙ presCupInt zero b two a
                              ∙ gradCommRing CP² _ _ _ _
    presCupInt two a one b  = sym (base-neutral _)
                              ∙ cong (base 6) (unitGroupEq (Hⁿ-CP²≅0 _ (compute-eqℕ _ _) (compute-eqℕ _ _)) _ _)
    presCupInt two a two b  = sym (base-neutral _)
                              ∙ cong (base 8) (unitGroupEq (Hⁿ-CP²≅0 _ (compute-eqℕ _ _) (compute-eqℕ _ _)) _ _)
    presCupInt two a (suc (suc (suc l))) b = refl
    presCupInt (suc (suc (suc k))) a l b = refl


    presCupVec : (v : Vec ℕ 1) → (a : ℤ) → (v' : Vec ℕ 1) → (b : ℤ) →
                  ℤ[x]→H*-CP² (base v a ·Pℤ base v' b)
                ≡ ℤ[x]→H*-CP² (base v a) cup ℤ[x]→H*-CP² (base v' b)
    presCupVec (k ∷ []) a (l ∷ []) b = presCupInt k a l b


    -- proof
    presCup : (x y : ℤ[x]) → ℤ[x]→H*-CP² (x ·Pℤ y) ≡ ℤ[x]→H*-CP² x cup ℤ[x]→H*-CP² y
    presCup = DS-Ind-Prop.f _ _ _ _
                           (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
                           (λ y → refl)
                           base-case
                           λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
      where
      base-case : _
      base-case (k ∷ []) a = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
                             (sym (RingTheory.0RightAnnihilates (H*R CP²) _))
                             (λ v' b → presCupVec (k ∷ []) a v' b)
                             λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*DistR+ _ _ _)



    -- Function on ℤ[x]/x + morphism
    ℤ[x]→H*-CP²-cancelX : (k : Fin 1) → ℤ[x]→H*-CP² (<X³> k) ≡ 0H*
    ℤ[x]→H*-CP²-cancelX zero = refl

    ℤ[X]→H*-CP² : RingHom (CommRing→Ring ℤ[X]) (H*R CP²)
    fst ℤ[X]→H*-CP² = ℤ[x]→H*-CP²
    snd ℤ[X]→H*-CP² = makeIsRingHom ℤ[x]→H*-CP²-pres1 ℤ[x]→H*-CP²-map+ presCup

    ℤ[X]/X³→H*R-CP² : RingHom (CommRing→Ring ℤ[X]/X³) (H*R CP²)
    ℤ[X]/X³→H*R-CP² = Quotient-FGideal-CommRing-Ring.inducedHom ℤ[X] (H*R CP²) ℤ[X]→H*-CP² <X³> ℤ[x]→H*-CP²-cancelX

    ℤ[x]/x³→H*-CP² : ℤ[x]/x³ → H* CP²
    ℤ[x]/x³→H*-CP² = fst ℤ[X]/X³→H*R-CP²



  -----------------------------------------------------------------------------
  -- Converse direction on ℤ[X] + ℤ[x]/x

    ϕ⁻¹ : (k : ℕ) → (a : coHom k CP²) → (x : partℕ k) → ℤ[x]
    ϕ⁻¹ k a (is0 x) = base (0 ∷ []) (ϕ₀⁻¹ (substG x a))
    ϕ⁻¹ k a (is2 x) = base (1 ∷ []) (ϕ₂⁻¹ (substG x a))
    ϕ⁻¹ k a (is4 x) = base (2 ∷ []) (ϕ₄⁻¹ (substG x a))
    ϕ⁻¹ k a (else x) = 0Pℤ

    H*-CP²→ℤ[x] : H* CP² → ℤ[x]
    H*-CP²→ℤ[x] = DS-Rec-Set.f _ _ _ _ isSetPℤ
         0Pℤ
         (λ k a → ϕ⁻¹ k a (part k))
         _+Pℤ_
         +PℤAssoc
         +PℤIdR
         +PℤComm
         (λ k → base-neutral-eq k (part k))
         λ k a b → base-add-eq k a b (part k)
      where

      base-neutral-eq : (k : ℕ) → (x : partℕ k) → ϕ⁻¹ k (0ₕ k) x ≡ 0Pℤ
      base-neutral-eq k (is0 x) = cong (base (0 ∷ [])) (cong ϕ₀⁻¹ (substG0 x))
                                  ∙ cong (base (0 ∷ [])) (pres1 ϕ₀⁻¹str)
                                  ∙ base-neutral (0 ∷ [])
      base-neutral-eq k (is2 x) = cong (base (1 ∷ [])) (cong ϕ₂⁻¹ (substG0 x))
                                  ∙ cong (base (1 ∷ [])) (pres1 ϕ₂⁻¹str)
                                  ∙ base-neutral (1 ∷ [])
      base-neutral-eq k (is4 x) = cong (base (2 ∷ [])) (cong ϕ₄⁻¹ (substG0 x))
                                  ∙ cong (base (2 ∷ [])) (pres1 ϕ₄⁻¹str)
                                  ∙ base-neutral (2 ∷ [])
      base-neutral-eq k (else x) = refl


      base-add-eq : (k : ℕ) → (a b : coHom k CP²) → (x : partℕ k)
                    → ϕ⁻¹ k a x +Pℤ ϕ⁻¹ k b x ≡ ϕ⁻¹ k (a +ₕ b) x
      base-add-eq k a b (is0 x) = base-add _ _ _
                                  ∙ cong (base (0 ∷ [])) (sym (pres· ϕ₀⁻¹str _ _) ∙ cong ϕ₀⁻¹ (substG+ a b x))
      base-add-eq k a b (is2 x) = base-add _ _ _
                                  ∙ cong (base (1 ∷ [])) (sym (pres· ϕ₂⁻¹str _ _) ∙ cong ϕ₂⁻¹ (substG+ a b x))
      base-add-eq k a b (is4 x) = base-add _ _ _
                                  ∙ cong (base (2 ∷ [])) (sym (pres· ϕ₄⁻¹str _ _) ∙ cong ϕ₄⁻¹ (substG+ a b x))
      base-add-eq k a b (else x) = +PℤIdR _

    H*-CP²→ℤ[x]-gmorph : (x y : H* CP²) → H*-CP²→ℤ[x] ( x +H* y) ≡ H*-CP²→ℤ[x] x +Pℤ H*-CP²→ℤ[x] y
    H*-CP²→ℤ[x]-gmorph x y = refl

    H*-CP²→ℤ[x]/x³ : H* CP² → ℤ[x]/x³
    H*-CP²→ℤ[x]/x³ = [_] ∘ H*-CP²→ℤ[x]

    H*-CP²→ℤ[x]/x³-gmorph : (x y : H* CP²) → H*-CP²→ℤ[x]/x³ (x +H* y) ≡ (H*-CP²→ℤ[x]/x³ x) +PℤI (H*-CP²→ℤ[x]/x³ y)
    H*-CP²→ℤ[x]/x³-gmorph x y = refl


  -----------------------------------------------------------------------------
  -- Section

    e-sect-base : (k : ℕ) → (a : coHom k CP²) → (x : partℕ k) →
                  ℤ[x]/x³→H*-CP² [ (ϕ⁻¹ k a x) ] ≡ base k a
    e-sect-base k a (is0 x) = cong (base 0) (ϕ₀-sect (substG x a))
                              ∙ sym (constSubstCommSlice (λ x → coHom x CP²) (H* CP²) base x a)
    e-sect-base k a (is2 x) = cong (base 2) (ϕ₂-sect (substG x a))
                              ∙ sym (constSubstCommSlice (λ x → coHom x CP²) (H* CP²) base x a)
    e-sect-base k a (is4 x) = cong (base 4) (ϕ₄-sect (substG x a))
                              ∙ sym (constSubstCommSlice (λ x → coHom x CP²) (H* CP²) base x a)
    e-sect-base k a (else x) = sym (base-neutral k)
                               ∙ cong (base k) (unitGroupSEq (sym (suc-predℕ k (fst x)))
                                                                (Hⁿ-CP²≅0 (predℕ k)
                                                                (λ p → fst (snd x) (suc-predℕ k (fst x) ∙ p))
                                                                 λ p → snd (snd x) (suc-predℕ k (fst x) ∙ p)) _ _)

    e-sect : (x : H* CP²) → ℤ[x]/x³→H*-CP² (H*-CP²→ℤ[x]/x³ x) ≡ x
    e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
             refl
             (λ k a → e-sect-base k a (part k))
             λ {U V} ind-U ind-V → cong₂ _+H*_ ind-U ind-V


  -----------------------------------------------------------------------------
  -- Retraction

    e-retr : (x : ℤ[x]/x³) → H*-CP²→ℤ[x]/x³ (ℤ[x]/x³→H*-CP² x) ≡ x
    e-retr = SQ.elimProp (λ _ → isSetPℤI _ _)
             (DS-Ind-Prop.f _ _ _ _ (λ _ → isSetPℤI _ _)
             refl
             base-case
             λ {U V} ind-U ind-V → cong₂ _+PℤI_ ind-U ind-V)
             where
             base-case : _
             base-case (zero ∷ []) a = cong [_] (cong (base (0 ∷ [])) (cong ϕ₀⁻¹ (transportRefl (ϕ₀ a))))
                                        ∙ cong [_] (cong (base (0 ∷ [])) (ϕ₀-retr a))
             base-case (one ∷ []) a = cong [_] (cong (base (1 ∷ [])) (cong ϕ₂⁻¹ (transportRefl (ϕ₂ a))))
                                      ∙ cong [_] (cong (base (1 ∷ [])) (ϕ₂-retr a))
             base-case (two ∷ []) a = cong [_] (cong (base (2 ∷ [])) (cong ϕ₄⁻¹ (transportRefl (ϕ₄ a))))
                                      ∙ cong [_] (cong (base (2 ∷ [])) (ϕ₄-retr a))
             base-case (suc (suc (suc k)) ∷ []) a = eq/ 0Pℤ (base (suc (suc (suc k)) ∷ []) a)
                                                    ∣ ((λ x → base (k ∷ []) (-ℤ a)) , helper) ∣₁
               where
               helper : _
               helper = (+PℤIdL _)
                        ∙ cong₂ base (cong (λ X → X ∷ []) (sym (+n-comm k 3)))
                                     (sym (·ℤIdR _))
                        ∙ (sym (+PℤIdR _))


-- End of the functions
-----------------------------------------------------------------------------


-----------------------------------------------------------------------------
-- Computation of the Cohomology Ring

open ComputeCP²Notation
     (invGroupIso H⁰CP²≅ℤ)
     (invGroupIso H²CP²≅ℤ)
     (invGroupIso H⁴CP²≅ℤ-pos)

ϕ₀-pres1 : ϕ₀ 1 ≡ 1⌣
ϕ₀-pres1 = refl

ϕ₀-gen : (n : ℕ) → (f : coHom n CP²) → ϕ₀ (pos 1) ⌣ f ≡ f
ϕ₀-gen n = ST.elim (λ _ → isProp→isSet (GroupStr.is-set (snd (coHomGr n CP²)) _ _))
             λ f → cong ∣_∣₂ (funExt (λ x → rUnitₖ n (f x)))

ϕ₂⌣ϕ₂≡ϕ₄ : ϕ₂ (pos 1) ⌣ ϕ₂ (pos 1) ≡ ϕ₄ (pos 1)
ϕ₂⌣ϕ₂≡ϕ₄ = H⁴CP²≅ℤ-pos-resp⌣

open ComputeCP²Function ϕ₀-pres1 ϕ₀-gen ϕ₂⌣ϕ₂≡ϕ₄

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
CohomologyRing-CP² = RingEquivs.invRingEquiv CP²-CohomologyRing
