{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.CommAlgebra.Localisation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
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
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Properties

open import Cubical.Tactics.CommRingSolver

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT


private
  variable
    ℓ ℓ′ : Level



module AlgLoc (R' : CommRing ℓ)
              (S' : ℙ (fst R')) (SMultClosedSubset : isMultClosedSubset R' S') where
 open isMultClosedSubset
 private R = fst R'
 open CommAlgebraStr
 open IsAlgebraHom
 open CommRingStr (snd R') renaming (_+_ to _+r_ ; _·_ to _·r_ ; ·IdR to ·rRid)
 open RingTheory (CommRing→Ring R')
 open CommRingTheory R'
 open Loc R' S' SMultClosedSubset
 open S⁻¹RUniversalProp R' S' SMultClosedSubset
 open CommAlgChar R'


 S⁻¹RAsCommAlg : CommAlgebra R' ℓ
 S⁻¹RAsCommAlg = toCommAlg (S⁻¹RAsCommRing , /1AsCommRingHom)

 LocCommAlg→CommRingPath : CommAlgebra→CommRing S⁻¹RAsCommAlg ≡ S⁻¹RAsCommRing
 LocCommAlg→CommRingPath = CommAlgebra→CommRing≡ (S⁻¹RAsCommRing , /1AsCommRingHom)

 hasLocAlgUniversalProp : (A : CommAlgebra R' ℓ)
                        → (∀ s → s ∈ S' → _⋆_ (snd A) s (1a (snd A)) ∈ (CommAlgebra→CommRing A) ˣ)
                        → Type (ℓ-suc ℓ)
 hasLocAlgUniversalProp A _ = (B : CommAlgebra R' ℓ)
                      → (∀ s → s ∈ S' →  _⋆_ (snd B) s (1a (snd B)) ∈ (CommAlgebra→CommRing B) ˣ)
                      → isContr (CommAlgebraHom A B)

 S⋆1⊆S⁻¹Rˣ : ∀ s → s ∈ S' → _⋆_ (snd S⁻¹RAsCommAlg) s (1a (snd S⁻¹RAsCommAlg)) ∈ S⁻¹Rˣ
 S⋆1⊆S⁻¹Rˣ s s∈S' = subst-∈ S⁻¹Rˣ
                    (cong [_] (≡-× (sym (·rRid s)) (Σ≡Prop (λ x → S' x .snd) (sym (·rRid _)))))
                    (S/1⊆S⁻¹Rˣ s s∈S')


 S⁻¹RHasAlgUniversalProp : hasLocAlgUniversalProp S⁻¹RAsCommAlg S⋆1⊆S⁻¹Rˣ
 S⁻¹RHasAlgUniversalProp B' S⋆1⊆Bˣ = χᴬ , χᴬuniqueness
  where
  B = fromCommAlg B' .fst
  φ = fromCommAlg B' .snd
  open CommRingStr (snd B) renaming (_·_ to _·b_ ; 1r to 1b ; ·IdL to ·bLid)

  χ : CommRingHom S⁻¹RAsCommRing B
  χ = S⁻¹RHasUniversalProp B φ S⋆1⊆Bˣ .fst .fst

  χcomp : ∀ r → fst χ (r /1) ≡ fst φ r
  χcomp = funExt⁻ (S⁻¹RHasUniversalProp B φ S⋆1⊆Bˣ .fst .snd)

  χᴬ : CommAlgebraHom S⁻¹RAsCommAlg B'
  fst χᴬ = fst χ
  pres0 (snd χᴬ) = IsRingHom.pres0 (snd χ)
  pres1 (snd χᴬ) = IsRingHom.pres1 (snd χ)
  pres+ (snd χᴬ) = IsRingHom.pres+ (snd χ)
  pres· (snd χᴬ) = IsRingHom.pres· (snd χ)
  pres- (snd χᴬ) = IsRingHom.pres- (snd χ)
  pres⋆ (snd χᴬ) r x = path
   where
   path : fst χ ((r /1) ·ₗ x) ≡ _⋆_  (snd B') r (fst χ x)
   path = fst χ ((r /1) ·ₗ x)             ≡⟨ IsRingHom.pres· (snd χ) _ _ ⟩
          fst χ (r /1) ·b fst χ x         ≡⟨ cong (_·b fst χ x) (χcomp r) ⟩
          fst φ r ·b fst χ x              ≡⟨ refl ⟩
          _⋆_  (snd B') r 1b ·b fst χ x   ≡⟨ ⋆AssocL (snd B') _ _ _ ⟩
          _⋆_  (snd B') r (1b ·b fst χ x) ≡⟨ cong (_⋆_ (snd B') r) (·bLid _) ⟩
          _⋆_  (snd B') r (fst χ x)       ∎


  χᴬuniqueness : (ψ : CommAlgebraHom S⁻¹RAsCommAlg B') → χᴬ ≡ ψ
  χᴬuniqueness ψ = Σ≡Prop (λ _ → isPropIsAlgebraHom _ _ _ _)
                          (cong (fst ∘ fst) (χuniqueness (ψ' , funExt ψ'r/1≡φr)))
   where
   χuniqueness = S⁻¹RHasUniversalProp B φ S⋆1⊆Bˣ .snd

   ψ' : CommRingHom S⁻¹RAsCommRing B
   fst ψ' = fst ψ
   IsRingHom.pres0 (snd ψ') = pres0 (snd ψ)
   IsRingHom.pres1 (snd ψ') = pres1 (snd ψ)
   IsRingHom.pres+ (snd ψ') = pres+ (snd ψ)
   IsRingHom.pres· (snd ψ') = pres· (snd ψ)
   IsRingHom.pres- (snd ψ') = pres- (snd ψ)

   ψ'r/1≡φr : ∀ r → fst ψ (r /1) ≡ fst φ r
   ψ'r/1≡φr r =
    fst ψ (r /1) ≡⟨ cong (fst ψ) (sym (·ₗ-rid _)) ⟩
    fst ψ (_⋆_ (snd S⁻¹RAsCommAlg) r (1a (snd S⁻¹RAsCommAlg))) ≡⟨ pres⋆ (snd ψ) _ _ ⟩
    _⋆_  (snd B') r (fst ψ (1a (snd S⁻¹RAsCommAlg))) ≡⟨ cong (_⋆_ (snd B') r) (pres1 (snd ψ)) ⟩
    _⋆_  (snd B') r 1b ∎


 -- an immediate corollary:
 isContrHomS⁻¹RS⁻¹R : isContr (CommAlgebraHom S⁻¹RAsCommAlg S⁻¹RAsCommAlg)
 isContrHomS⁻¹RS⁻¹R = S⁻¹RHasAlgUniversalProp S⁻¹RAsCommAlg S⋆1⊆S⁻¹Rˣ

 S⁻¹RAlgCharEquiv : (A' : CommRing ℓ) (φ : CommRingHom R' A')
                  → PathToS⁻¹R  R' S' SMultClosedSubset A' φ
                  → CommAlgebraEquiv S⁻¹RAsCommAlg (toCommAlg (A' , φ))
 S⁻¹RAlgCharEquiv A' φ cond = toCommAlgebraEquiv (S⁻¹RAsCommRing , /1AsCommRingHom) (A' , φ)
                                (S⁻¹RCharEquiv R' S' SMultClosedSubset A' φ cond)
                                (RingHom≡ (S⁻¹RHasUniversalProp A' φ (cond .φS⊆Aˣ) .fst .snd))
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
  invElCommAlgebra→CommRingPath = LocCommAlg→CommRingPath

module AlgLocTwoSubsets (R' : CommRing ℓ)
                        (S₁ : ℙ (fst R')) (S₁MultClosedSubset : isMultClosedSubset R' S₁)
                        (S₂ : ℙ (fst R')) (S₂MultClosedSubset : isMultClosedSubset R' S₂) where
 open isMultClosedSubset
 open CommRingStr (snd R') hiding (is-set)
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

 open IsAlgebraHom
 open AlgebraHoms
 open CommAlgebraHoms
 open CommAlgebraStr ⦃...⦄

 private
  R = fst R'
  S₁⁻¹Rˣ = S₁⁻¹RAsCommRing ˣ
  S₂⁻¹Rˣ = S₂⁻¹RAsCommRing ˣ
  instance
   _ = snd S₁⁻¹RAsCommAlg
   _ = snd S₂⁻¹RAsCommAlg


 isContrS₁⁻¹R≡S₂⁻¹R : (∀ s₁ → s₁ ∈ S₁ → s₁ ⋆ 1a ∈ S₂⁻¹Rˣ)
                    → (∀ s₂ → s₂ ∈ S₂ → s₂ ⋆ 1a ∈ S₁⁻¹Rˣ)
                    → isContr (S₁⁻¹RAsCommAlg ≡ S₂⁻¹RAsCommAlg)
 isContrS₁⁻¹R≡S₂⁻¹R S₁⊆S₂⁻¹Rˣ S₂⊆S₁⁻¹Rˣ = isOfHLevelRetractFromIso 0
                                            (equivToIso (invEquiv (CommAlgebraPath _ _ _)))
                                              isContrS₁⁻¹R≅S₂⁻¹R
  where
  χ₁ : CommAlgebraHom S₁⁻¹RAsCommAlg S₂⁻¹RAsCommAlg
  χ₁ = S₁⁻¹RHasAlgUniversalProp S₂⁻¹RAsCommAlg S₁⊆S₂⁻¹Rˣ .fst

  χ₂ : CommAlgebraHom S₂⁻¹RAsCommAlg S₁⁻¹RAsCommAlg
  χ₂ = S₂⁻¹RHasAlgUniversalProp S₁⁻¹RAsCommAlg S₂⊆S₁⁻¹Rˣ .fst

  χ₁∘χ₂≡id : χ₁ ∘a χ₂ ≡ idCommAlgebraHom _
  χ₁∘χ₂≡id = isContr→isProp isContrHomS₂⁻¹RS₂⁻¹R _ _

  χ₂∘χ₁≡id : χ₂ ∘a χ₁ ≡ idCommAlgebraHom _
  χ₂∘χ₁≡id = isContr→isProp isContrHomS₁⁻¹RS₁⁻¹R _ _

  IsoS₁⁻¹RS₂⁻¹R : Iso S₁⁻¹R S₂⁻¹R
  Iso.fun IsoS₁⁻¹RS₂⁻¹R = fst χ₁
  Iso.inv IsoS₁⁻¹RS₂⁻¹R = fst χ₂
  Iso.rightInv IsoS₁⁻¹RS₂⁻¹R = funExt⁻ (cong fst χ₁∘χ₂≡id)
  Iso.leftInv IsoS₁⁻¹RS₂⁻¹R = funExt⁻ (cong fst χ₂∘χ₁≡id)

  isContrS₁⁻¹R≅S₂⁻¹R : isContr (CommAlgebraEquiv S₁⁻¹RAsCommAlg S₂⁻¹RAsCommAlg)
  isContrS₁⁻¹R≅S₂⁻¹R = center , uniqueness
   where
   center : CommAlgebraEquiv S₁⁻¹RAsCommAlg S₂⁻¹RAsCommAlg
   fst center = isoToEquiv IsoS₁⁻¹RS₂⁻¹R
   pres0 (snd center) = pres0 (snd χ₁)
   pres1 (snd center) = pres1 (snd χ₁)
   pres+ (snd center) = pres+ (snd χ₁)
   pres· (snd center) = pres· (snd χ₁)
   pres- (snd center) = pres- (snd χ₁)
   pres⋆ (snd center) = pres⋆ (snd χ₁)

   uniqueness : (φ : CommAlgebraEquiv S₁⁻¹RAsCommAlg S₂⁻¹RAsCommAlg) → center ≡ φ
   uniqueness φ = Σ≡Prop (λ _ → isPropIsAlgebraHom _ _ _ _)
                         (equivEq (cong fst
                           (S₁⁻¹RHasAlgUniversalProp S₂⁻¹RAsCommAlg S₁⊆S₂⁻¹Rˣ .snd
                             (AlgebraEquiv→AlgebraHom φ))))


 isPropS₁⁻¹R≡S₂⁻¹R  : isProp (S₁⁻¹RAsCommAlg ≡ S₂⁻¹RAsCommAlg)
 isPropS₁⁻¹R≡S₂⁻¹R S₁⁻¹R≡S₂⁻¹R  =
   isContr→isProp (isContrS₁⁻¹R≡S₂⁻¹R  S₁⊆S₂⁻¹Rˣ S₂⊆S₁⁻¹Rˣ) S₁⁻¹R≡S₂⁻¹R
    where
    S₁⊆S₂⁻¹Rˣ : ∀ s₁ → s₁ ∈ S₁ → s₁ ⋆ 1a ∈ S₂⁻¹Rˣ
    S₁⊆S₂⁻¹Rˣ s₁ s₁∈S₁ =
      transport (λ i → _⋆_ ⦃ S₁⁻¹R≡S₂⁻¹R i .snd ⦄ s₁ (1a ⦃ S₁⁻¹R≡S₂⁻¹R i .snd ⦄)
                     ∈ (CommAlgebra→CommRing (S₁⁻¹R≡S₂⁻¹R i)) ˣ) (S₁⋆1⊆S₁⁻¹Rˣ s₁ s₁∈S₁)

    S₂⊆S₁⁻¹Rˣ : ∀ s₂ → s₂ ∈ S₂ → s₂ ⋆ 1a ∈ S₁⁻¹Rˣ
    S₂⊆S₁⁻¹Rˣ s₂ s₂∈S₂ =
      transport (λ i → _⋆_ ⦃ (sym S₁⁻¹R≡S₂⁻¹R) i .snd ⦄ s₂ (1a ⦃ (sym S₁⁻¹R≡S₂⁻¹R) i .snd ⦄)
                     ∈ (CommAlgebra→CommRing ((sym S₁⁻¹R≡S₂⁻¹R) i)) ˣ) (S₂⋆1⊆S₂⁻¹Rˣ s₂ s₂∈S₂)



-- A crucial result for the construction of the structure sheaf
module DoubleAlgLoc (R : CommRing ℓ) (f g : (fst R)) where
 open Exponentiation R
 open InvertingElementsBase
 open CommRingStr (snd R) hiding (·IdR)
 open isMultClosedSubset
 open DoubleLoc R f g hiding (R[1/fg]≡R[1/f][1/g])
 open CommAlgChar R
 open AlgLoc R ([_ⁿ|n≥0] R (f · g)) (powersFormMultClosedSubset R (f · g))
             renaming (S⁻¹RAlgCharEquiv to R[1/fg]AlgCharEquiv)
 open CommIdeal R hiding (subst-∈) renaming (_∈_ to _∈ᵢ_)
 open isCommIdeal
 open RadicalIdeal R

 private
  ⟨_⟩ : (fst R) → CommIdeal
  ⟨ f ⟩ = ⟨ replicateFinVec 1 f ⟩[ R ]

  R[1/fg]AsCommAlgebra = R[1/_]AsCommAlgebra {R = R} (f · g)
  R[1/fg]ˣ = R[1/_]AsCommRing R (f · g) ˣ

  R[1/g]AsCommAlgebra = R[1/_]AsCommAlgebra {R = R} g
  R[1/g]ˣ = R[1/_]AsCommRing R g ˣ

  R[1/f][1/g]AsCommRing = R[1/_]AsCommRing (R[1/_]AsCommRing R f)
                                [ g , 1r , powersFormMultClosedSubset R f .containsOne ]
  R[1/f][1/g]AsCommAlgebra = toCommAlg (R[1/f][1/g]AsCommRing , /1/1AsCommRingHom)

 R[1/fg]≡R[1/f][1/g] : R[1/fg]AsCommAlgebra ≡ R[1/f][1/g]AsCommAlgebra
 R[1/fg]≡R[1/f][1/g] = uaCommAlgebra (R[1/fg]AlgCharEquiv _ _ pathtoR[1/fg])

 doubleLocCancel : g ∈ᵢ √ ⟨ f ⟩ → R[1/f][1/g]AsCommAlgebra ≡ R[1/g]AsCommAlgebra
 doubleLocCancel g∈√⟨f⟩ = sym R[1/fg]≡R[1/f][1/g] ∙ isContrR[1/fg]≡R[1/g] toUnit1 toUnit2 .fst
  where
  open S⁻¹RUniversalProp R ([_ⁿ|n≥0] R g) (powersFormMultClosedSubset R g)
                           renaming (_/1 to _/1ᵍ)
  open S⁻¹RUniversalProp R ([_ⁿ|n≥0] R (f · g)) (powersFormMultClosedSubset R (f · g))
                           renaming (_/1 to _/1ᶠᵍ)
  open AlgLocTwoSubsets R ([_ⁿ|n≥0] R (f · g)) (powersFormMultClosedSubset R (f · g))
                          ([_ⁿ|n≥0] R g) (powersFormMultClosedSubset R g)
                          renaming (isContrS₁⁻¹R≡S₂⁻¹R to isContrR[1/fg]≡R[1/g])
  open CommAlgebraStr ⦃...⦄ hiding (_·_ ; _+_)
  instance
   _ = snd R[1/fg]AsCommAlgebra
   _ = snd R[1/g]AsCommAlgebra

  toUnit1 : ∀ s → s ∈ [_ⁿ|n≥0] R (f · g) → s ⋆ 1a ∈ R[1/g]ˣ
  toUnit1 s s∈[fgⁿ|n≥0] = subst-∈ R[1/g]ˣ (sym (·IdR (s /1ᵍ)))
                            (RadicalLemma.toUnit R g (f · g) (radHelper _ _ g∈√⟨f⟩) s s∈[fgⁿ|n≥0])
   where
   radHelper : ∀ x y → x ∈ᵢ √ ⟨ y ⟩ → x ∈ᵢ √ ⟨ y · x ⟩
   radHelper x y = PT.rec ((√ ⟨ y · x ⟩) .fst x .snd) (uncurry helper1)
    where
    helper1 : (n : ℕ) → x ^ n ∈ᵢ ⟨ y ⟩ → x ∈ᵢ √ ⟨ y · x ⟩
    helper1 n = PT.rec ((√ ⟨ y · x ⟩) .fst x .snd) (uncurry helper2)
     where
     helper2 : (α : FinVec (fst R) 1)
             → x ^ n ≡ linearCombination R α (replicateFinVec 1 y)
             → x ∈ᵢ √ ⟨ y · x ⟩
     helper2 α p = ∣ (suc n) , ∣ α , cong (x ·_) p ∙ solve! R ∣₁ ∣₁

  toUnit2 : ∀ s → s ∈ [_ⁿ|n≥0] R g → s ⋆ 1a ∈ R[1/fg]ˣ
  toUnit2 s s∈[gⁿ|n≥0] = subst-∈ R[1/fg]ˣ (sym (·IdR (s /1ᶠᵍ)))
                           (RadicalLemma.toUnit R (f · g) g radHelper s s∈[gⁿ|n≥0])
   where
   radHelper : (f · g) ∈ᵢ √ ⟨ g ⟩
   radHelper = ·Closed (snd (√ ⟨ g ⟩)) f (∈→∈√ _ _ (indInIdeal R _ zero))
