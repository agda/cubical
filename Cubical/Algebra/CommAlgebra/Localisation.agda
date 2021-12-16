{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommAlgebra.Localisation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma

open import Cubical.Reflection.StrictEquiv

open import Cubical.Structures.Axioms
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Algebra.CommRing.Localisation.UniversalProperty
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Properties

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
 open CommRingStr (snd R') renaming (_+_ to _+r_ ; _·_ to _·r_ ; ·Rid to ·rRid)
 open RingTheory (CommRing→Ring R')
 open CommRingTheory R'
 open Loc R' S' SMultClosedSubset
 open S⁻¹RUniversalProp R' S' SMultClosedSubset
 open CommAlgChar R'


 S⁻¹RAsCommAlg : CommAlgebra R' ℓ
 S⁻¹RAsCommAlg = toCommAlg (S⁻¹RAsCommRing , /1AsCommRingHom)


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
  open CommRingStr (snd B) renaming (_·_ to _·b_ ; 1r to 1b ; ·Lid to ·bLid)

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
          _⋆_  (snd B') r 1b ·b fst χ x   ≡⟨ ⋆-lassoc (snd B') _ _ _ ⟩
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

  χ₁∘χ₂≡id : χ₁ ∘a χ₂ ≡ idAlgHom
  χ₁∘χ₂≡id = isContr→isProp isContrHomS₂⁻¹RS₂⁻¹R _ _

  χ₂∘χ₁≡id : χ₂ ∘a χ₁ ≡ idAlgHom
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
