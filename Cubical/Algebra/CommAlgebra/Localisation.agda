{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.CommAlgebra.Localisation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure using (⟨_⟩; withOpaqueStr; makeOpaque)
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.FinData

open import Cubical.Reflection.StrictEquiv

open import Cubical.Structures.Axioms
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Algebra.CommRing.Localisation
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Univalence

open import Cubical.Tactics.CommRingSolver

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ′ : Level

module AlgLoc (R : CommRing ℓ)
              (S : ℙ ⟨ R ⟩) (SMultClosedSubset : isMultClosedSubset R S) where
 open isMultClosedSubset
 open CommRingStr ⦃...⦄
 open CommAlgebraStr ⦃...⦄
 open RingTheory (CommRing→Ring R)
 open CommRingTheory R
 open Loc R S SMultClosedSubset hiding (S)
 open S⁻¹RUniversalProp R S SMultClosedSubset
 open IsCommRingHom


 S⁻¹RAsCommAlg : CommAlgebra R ℓ
 S⁻¹RAsCommAlg = (S⁻¹RAsCommRing , /1AsCommRingHom)
 private instance
   _ = CommAlgebra→CommAlgebraStr S⁻¹RAsCommAlg
   _ = S⁻¹RAsCommAlg .fst .snd
   _ = R .snd

 module _ (A : CommAlgebra R ℓ) where
   private instance
     _ = CommAlgebra→CommAlgebraStr A
     _ = A .fst .snd

   hasLocAlgUniversalProp : (∀ s → s ∈ S → s ⋆ 1r ∈ A .fst ˣ)
                            → Type (ℓ-suc ℓ)
   hasLocAlgUniversalProp _ = (B : CommAlgebra R ℓ)
                               → (let instance
                                        _ = (CommAlgebra→CommAlgebraStr B)
                                        _ = B .fst .snd
                                  in ∀ s → s ∈ S → s ⋆ 1r ∈ B .fst ˣ)
                               → isContr (CommAlgebraHom A B)

 S⋆1⊆S⁻¹Rˣ : ∀ s → s ∈ S → s ⋆ 1r ∈ S⁻¹Rˣ
 S⋆1⊆S⁻¹Rˣ s s∈S' = subst-∈ S⁻¹Rˣ
                    (cong [_] (≡-× (sym (·IdR s)) (Σ≡Prop (λ x → S x .snd) (sym (·IdR _)))))
                    (S/1⊆S⁻¹Rˣ s s∈S')
 S⁻¹RHasAlgUniversalProp : hasLocAlgUniversalProp S⁻¹RAsCommAlg S⋆1⊆S⁻¹Rˣ
 S⁻¹RHasAlgUniversalProp B S⋆1⊆Bˣ' = χᴬ , χᴬuniqueness
  where
  φ = B .snd
  instance
    _ = CommAlgebra→CommAlgebraStr B
    _ = B .fst .snd

  S⋆1⊆Bˣ : (s : fst R) → s ∈ S → fst φ s ∈ (B .fst ˣ)
  S⋆1⊆Bˣ s s∈S = subst (_∈ (B .fst ˣ)) (·IdR _) (S⋆1⊆Bˣ' s s∈S)

  χ : CommRingHom S⁻¹RAsCommRing (B .fst)
  χ = S⁻¹RHasUniversalProp (B .fst) φ  S⋆1⊆Bˣ .fst .fst

  χcomp : ∀ r → fst χ (r /1) ≡ fst φ r
  χcomp = funExt⁻ (S⁻¹RHasUniversalProp (B .fst) φ  S⋆1⊆Bˣ  .fst .snd)

  χᴬ : CommAlgebraHom S⁻¹RAsCommAlg B
  χᴬ = CommAlgebraHomFromCommRingHom χ path
   where
   opaque
     path : ∀ r x → fst χ ((r /1) ·ₗ x) ≡ r ⋆ (fst χ x)
     path r x = fst χ ((r /1) ·ₗ x)      ≡⟨ IsCommRingHom.pres· (snd χ) _ _ ⟩
            fst χ (r /1) · fst χ x      ≡⟨ cong (_· fst χ x) (χcomp r) ⟩
            (B .snd .fst r) · (fst χ x) ≡⟨ cong (_· fst χ x) (sym (·IdR _)) ⟩
            (r  ⋆ 1r) · fst χ x         ≡⟨ ⋆AssocL _ _ _ ⟩
            r ⋆ (1r · fst χ x)          ≡⟨ cong (r ⋆_) (·IdL _) ⟩
            r ⋆ (fst χ x)       ∎

  χᴬuniqueness : (ψ : CommAlgebraHom S⁻¹RAsCommAlg B) → χᴬ ≡ ψ
  χᴬuniqueness ψ =
    CommAlgebraHom≡ {f = χᴬ}
      (χᴬ  .fst ≡⟨ cong (fst ∘ fst) (χuniqueness (CommAlgebraHom→CommRingHom ψ , funExt ψ'r/1≡φr)) ⟩ ψ .fst ∎)

   where
   χuniqueness = S⁻¹RHasUniversalProp (B .fst) φ  S⋆1⊆Bˣ .snd

   ψ'r/1≡φr : ∀ r → ψ .fst (r /1) ≡ fst φ r
   ψ'r/1≡φr r =
    ψ .fst (r /1)    ≡⟨ cong (ψ .fst) (sym (·ₗ-rid _)) ⟩
    ψ .fst (r ⋆ 1r)  ≡⟨ IsCommAlgebraHom.pres⋆ (ψ .snd) _ _ ⟩
    r ⋆ (ψ .fst 1r)  ≡⟨ cong (λ u → r ⋆ u) (IsCommAlgebraHom.pres1 (ψ .snd))  ⟩
    r ⋆ 1r           ≡⟨ solve! (B .fst) ⟩
    fst φ r ∎


 -- an immediate corollary:
 isContrHomS⁻¹RS⁻¹R : isContr (CommAlgebraHom S⁻¹RAsCommAlg S⁻¹RAsCommAlg)
 isContrHomS⁻¹RS⁻¹R = S⁻¹RHasAlgUniversalProp S⁻¹RAsCommAlg S⋆1⊆S⁻¹Rˣ

 S⁻¹RAlgCharEquiv : (A : CommRing ℓ) (φ : CommRingHom R A)
                  → PathToS⁻¹R  R S SMultClosedSubset A φ
                  → CommAlgebraEquiv S⁻¹RAsCommAlg (A , φ)
 S⁻¹RAlgCharEquiv A φ cond =
   CommRingEquiv→CommAlgebraEquiv
     (S⁻¹RCharEquiv R S SMultClosedSubset A φ cond)
     (S⁻¹RHasUniversalProp A φ (cond .φS⊆Aˣ) .fst .snd)
    where open PathToS⁻¹R

-- the special case of localizing at a single element
R[1/_]AsCommAlgebra : {R : CommRing ℓ} → fst R → CommAlgebra R ℓ
R[1/_]AsCommAlgebra {R = R} f = S⁻¹RAsCommAlg [ f ⁿ|n≥0] (powersFormMultClosedSubset f)
 where
 open AlgLoc R
 open InvertingElementsBase R

module _  {R : CommRing ℓ} (f : fst R) where
  open InvertingElementsBase R
  open AlgLoc R [ f ⁿ|n≥0] (powersFormMultClosedSubset f)

  invElCommAlgebra→CommRingPath : CommAlgebra→CommRing R[1/ f ]AsCommAlgebra ≡ R[1/ f ]AsCommRing
  invElCommAlgebra→CommRingPath = refl

module AlgLocTwoSubsets (R' : CommRing ℓ)
                        (S₁ : ℙ (fst R')) (S₁MultClosedSubset : isMultClosedSubset R' S₁)
                        (S₂ : ℙ (fst R')) (S₂MultClosedSubset : isMultClosedSubset R' S₂) where
 open isMultClosedSubset
 open RingTheory (CommRing→Ring R')
 open Loc R' S₁ S₁MultClosedSubset renaming (S⁻¹R to S₁⁻¹R ;
                                             S⁻¹RAsCommRing to S₁⁻¹RAsCommRing)
 open Loc R' S₂ S₂MultClosedSubset renaming (S⁻¹R to S₂⁻¹R ;
                                             S⁻¹RAsCommRing to S₂⁻¹RAsCommRing)
 open AlgLoc R' S₁ S₁MultClosedSubset renaming ( S⁻¹RAsCommAlg to S₁⁻¹RAsCommAlg
                                               ; S⋆1⊆S⁻¹Rˣ to S₁⋆1⊆S₁⁻¹Rˣ
                                               ; S⁻¹RHasAlgUniversalProp to S₁⁻¹RHasAlgUniversalProp
                                               ; isContrHomS⁻¹RS⁻¹R to isContrHomS₁⁻¹RS₁⁻¹R)
 open AlgLoc R' S₂ S₂MultClosedSubset renaming ( S⁻¹RAsCommAlg to S₂⁻¹RAsCommAlg
                                               ; S⋆1⊆S⁻¹Rˣ to S₂⋆1⊆S₂⁻¹Rˣ
                                               ; S⁻¹RHasAlgUniversalProp to S₂⁻¹RHasAlgUniversalProp
                                               ; isContrHomS⁻¹RS⁻¹R to isContrHomS₂⁻¹RS₂⁻¹R)

 open CommAlgebraStr ⦃...⦄
 open CommRingStr ⦃...⦄

 private
  S₁⁻¹Rˣ = S₁⁻¹RAsCommRing ˣ
  S₂⁻¹Rˣ = S₂⁻¹RAsCommRing ˣ
  instance
    _ = CommAlgebra→CommAlgebraStr S₁⁻¹RAsCommAlg
    _ = CommAlgebra→CommAlgebraStr S₂⁻¹RAsCommAlg
    _ = S₂⁻¹RAsCommAlg .fst .snd
    _ = S₁⁻¹RAsCommAlg .fst .snd
    _ = R' .snd


 isContrS₁⁻¹R≡S₂⁻¹R : (∀ (s₁ : ⟨ R' ⟩) → s₁ ∈ S₁ → s₁ ⋆ 1r ∈ S₂⁻¹Rˣ)
                    → (∀ s₂ → s₂ ∈ S₂ → s₂ ⋆ 1r ∈ S₁⁻¹Rˣ)
                    → isContr (S₁⁻¹RAsCommAlg ≡ S₂⁻¹RAsCommAlg)
 isContrS₁⁻¹R≡S₂⁻¹R S₁⊆S₂⁻¹Rˣ S₂⊆S₁⁻¹Rˣ = isOfHLevelRetractFromIso 0
                                            (equivToIso (invEquiv (CommAlgebraPath _ _)))
                                             isContrS₁⁻¹R≅S₂⁻¹R
  where
  χ₁ : CommAlgebraHom S₁⁻¹RAsCommAlg S₂⁻¹RAsCommAlg
  χ₁ = S₁⁻¹RHasAlgUniversalProp S₂⁻¹RAsCommAlg S₁⊆S₂⁻¹Rˣ .fst

  χ₂ : CommAlgebraHom S₂⁻¹RAsCommAlg S₁⁻¹RAsCommAlg
  χ₂ = S₂⁻¹RHasAlgUniversalProp S₁⁻¹RAsCommAlg S₂⊆S₁⁻¹Rˣ .fst

  χ₁∘χ₂≡id : χ₁ ∘ca χ₂ ≡ idCAlgHom _
  χ₁∘χ₂≡id = isContr→isProp isContrHomS₂⁻¹RS₂⁻¹R _ _

  χ₂∘χ₁≡id : χ₂ ∘ca χ₁ ≡ idCAlgHom _
  χ₂∘χ₁≡id = isContr→isProp isContrHomS₁⁻¹RS₁⁻¹R _ _

  IsoS₁⁻¹RS₂⁻¹R : Iso S₁⁻¹R S₂⁻¹R
  Iso.fun IsoS₁⁻¹RS₂⁻¹R = ⟨ χ₁ ⟩ₐ→
  Iso.inv IsoS₁⁻¹RS₂⁻¹R = ⟨ χ₂ ⟩ₐ→
  Iso.rightInv IsoS₁⁻¹RS₂⁻¹R = funExt⁻ (cong ⟨_⟩ₐ→ χ₁∘χ₂≡id)
  Iso.leftInv IsoS₁⁻¹RS₂⁻¹R = funExt⁻ (cong ⟨_⟩ₐ→ χ₂∘χ₁≡id)

  isContrS₁⁻¹R≅S₂⁻¹R : isContr (CommAlgebraEquiv S₁⁻¹RAsCommAlg S₂⁻¹RAsCommAlg)
  isContrS₁⁻¹R≅S₂⁻¹R = center , uniqueness
   where
   X₁asCRHom = CommAlgebraHom→CommRingHom χ₁
   center : CommAlgebraEquiv S₁⁻¹RAsCommAlg S₂⁻¹RAsCommAlg
   center =
     CommRingEquiv→CommAlgebraEquiv
       ((isoToEquiv IsoS₁⁻¹RS₂⁻¹R) , snd X₁asCRHom)
       (cong fst (CommAlgebraHom→Triangle χ₁))

   uniqueness : (φ : CommAlgebraEquiv S₁⁻¹RAsCommAlg S₂⁻¹RAsCommAlg) → center ≡ φ
   uniqueness φ =
     CommAlgebraEquiv≡ (cong ⟨_⟩ₐ→ $ S₁⁻¹RHasAlgUniversalProp S₂⁻¹RAsCommAlg S₁⊆S₂⁻¹Rˣ .snd
                             (CommAlgebraEquiv→CommAlgebraHom φ))


 opaque
   isPropS₁⁻¹R≡S₂⁻¹R  : isProp (S₁⁻¹RAsCommAlg ≡ S₂⁻¹RAsCommAlg)
   isPropS₁⁻¹R≡S₂⁻¹R S₁⁻¹R≡S₂⁻¹R  =
     isContr→isProp (isContrS₁⁻¹R≡S₂⁻¹R  S₁⊆S₂⁻¹Rˣ S₂⊆S₁⁻¹Rˣ) S₁⁻¹R≡S₂⁻¹R
      where

      S₁⊆S₂⁻¹Rˣ : ∀ s₁ → s₁ ∈ S₁ → s₁ ⋆ 1r ∈ S₂⁻¹Rˣ
      S₁⊆S₂⁻¹Rˣ s₁ s₁∈S₁ =
        transport (λ i → let instance
                             _ = (S₁⁻¹R≡S₂⁻¹R i) .fst .snd
                             _ = CommAlgebra→CommAlgebraStr (S₁⁻¹R≡S₂⁻¹R i)
                          in s₁ ⋆ 1r ∈ (CommAlgebra→CommRing (S₁⁻¹R≡S₂⁻¹R i)) ˣ) (S₁⋆1⊆S₁⁻¹Rˣ s₁ s₁∈S₁)

      S₂⊆S₁⁻¹Rˣ : ∀ s₂ → s₂ ∈ S₂ → s₂ ⋆ 1r ∈ S₁⁻¹Rˣ
      S₂⊆S₁⁻¹Rˣ s₂ s₂∈S₂ =
        transport (λ i → let instance
                             _ = ((sym S₁⁻¹R≡S₂⁻¹R) i) .fst .snd
                             _ = CommAlgebra→CommAlgebraStr ((sym S₁⁻¹R≡S₂⁻¹R) i)
                         in s₂ ⋆ 1r ∈ (CommAlgebra→CommRing ((sym S₁⁻¹R≡S₂⁻¹R) i)) ˣ) (S₂⋆1⊆S₂⁻¹Rˣ s₂ s₂∈S₂)


-- A crucial result for the construction of the structure sheaf
module DoubleAlgLoc (R : CommRing ℓ) (f g : (fst R)) where
 open CommRingStr ⦃...⦄
 private instance
   _ = R .snd
 open Exponentiation R
 open InvertingElementsBase
 open isMultClosedSubset
 open DoubleLoc R f g hiding (R[1/fg]≡R[1/f][1/g])
 open AlgLoc R ([_ⁿ|n≥0] R (f · g)) (powersFormMultClosedSubset R (f · g))
             renaming (S⁻¹RAlgCharEquiv to R[1/fg]AlgCharEquiv)
 open CommIdeal R hiding (subst-∈) renaming (_∈_ to _∈ᵢ_)
 open isCommIdeal
 open RadicalIdeal R


 private
  ⟨_⟩ᵢ : (fst R) → CommIdeal
  ⟨ f ⟩ᵢ = ⟨ replicateFinVec 1 f ⟩[ R ]

  R[1/fg]AsCommAlgebra = R[1/_]AsCommAlgebra {R = R} (f · g)
  R[1/fg]ˣ = R[1/_]AsCommRing R (f · g) ˣ

  R[1/g]AsCommAlgebra = R[1/_]AsCommAlgebra {R = R} g
  R[1/g]ˣ = R[1/_]AsCommRing R g ˣ

  R[1/f][1/g]AsCommRing = R[1/_]AsCommRing (R[1/_]AsCommRing R f)
                                [ g , 1r , powersFormMultClosedSubset R f .containsOne ]

  R[1/f][1/g]AsCommAlgebra : CommAlgebra R _
  R[1/f][1/g]AsCommAlgebra = R[1/f][1/g]AsCommRing , /1/1AsCommRingHom

 R[1/fg]≡R[1/f][1/g] : R[1/fg]AsCommAlgebra ≡ R[1/f][1/g]AsCommAlgebra
 R[1/fg]≡R[1/f][1/g] = uaCommAlgebra (R[1/fg]AlgCharEquiv _ _ pathtoR[1/fg])

 doubleLocCancel : g ∈ᵢ √ ⟨ f ⟩ᵢ → R[1/f][1/g]AsCommAlgebra ≡ R[1/g]AsCommAlgebra
 doubleLocCancel g∈√⟨f⟩ = sym R[1/fg]≡R[1/f][1/g] ∙ isContrR[1/fg]≡R[1/g] toUnit1 toUnit2 .fst
  where
  open S⁻¹RUniversalProp R ([_ⁿ|n≥0] R g) (powersFormMultClosedSubset R g)
                           renaming (_/1 to _/1ᵍ)
  open S⁻¹RUniversalProp R ([_ⁿ|n≥0] R (f · g)) (powersFormMultClosedSubset R (f · g))
                           renaming (_/1 to _/1ᶠᵍ)
  open AlgLocTwoSubsets R ([_ⁿ|n≥0] R (f · g)) (powersFormMultClosedSubset R (f · g))
                          ([_ⁿ|n≥0] R g) (powersFormMultClosedSubset R g)
                          renaming (isContrS₁⁻¹R≡S₂⁻¹R to isContrR[1/fg]≡R[1/g])
  open CommAlgebraStr ⦃...⦄
  instance
   _ = CommAlgebra→CommAlgebraStr R[1/fg]AsCommAlgebra
   _ = CommAlgebra→CommAlgebraStr R[1/g]AsCommAlgebra
   _ = R[1/fg]AsCommAlgebra .fst .snd
   _ = R[1/g]AsCommAlgebra .fst .snd

  toUnit1 : ∀ s → s ∈ [_ⁿ|n≥0] R (f · g) → s ⋆ 1r ∈ R[1/g]ˣ
  toUnit1 s s∈[fgⁿ|n≥0] = subst-∈ R[1/g]ˣ (sym (·IdR (s /1ᵍ)))
                            (RadicalLemma.toUnit R g (f · g) (radHelper _ _ g∈√⟨f⟩) s s∈[fgⁿ|n≥0])
   where
   radHelper : ∀ x y → x ∈ᵢ √ ⟨ y ⟩ᵢ → x ∈ᵢ √ ⟨ y · x ⟩ᵢ
   radHelper x y = PT.rec ((√ ⟨ y · x ⟩ᵢ) .fst x .snd) (uncurry helper1)
    where
    helper1 : (n : ℕ) → x ^ n ∈ᵢ ⟨ y ⟩ᵢ → x ∈ᵢ √ ⟨ y · x ⟩ᵢ
    helper1 n = PT.rec ((√ ⟨ y · x ⟩ᵢ) .fst x .snd) (uncurry helper2)
     where
     helper2 : (α : FinVec (fst R) 1)
             → x ^ n ≡ linearCombination R α (replicateFinVec 1 y)
             → x ∈ᵢ √ ⟨ y · x ⟩ᵢ
     helper2 α p = ∣ (suc n) , ∣ α , cong (x ·_) p ∙ solve! R ∣₁ ∣₁

  toUnit2 : ∀ s → s ∈ [_ⁿ|n≥0] R g → s ⋆ 1r ∈ R[1/fg]ˣ
  toUnit2 s s∈[gⁿ|n≥0] = subst-∈ R[1/fg]ˣ (sym (·IdR (s /1ᶠᵍ)))
                           (RadicalLemma.toUnit R (f · g) g radHelper s s∈[gⁿ|n≥0])
   where
   radHelper : (f · g) ∈ᵢ √ ⟨ g ⟩ᵢ
   radHelper = ·Closed (snd (√ ⟨ g ⟩ᵢ)) f (∈→∈√ _ _ (indInIdeal R _ zero))
