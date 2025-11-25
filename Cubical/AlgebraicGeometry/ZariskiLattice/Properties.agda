{-# OPTIONS --lossy-unification #-}
module Cubical.AlgebraicGeometry.ZariskiLattice.Properties where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset using (ℙ)
                                         renaming (_∈_ to _∈ₚ_ ; ∈-isProp to ∈ₚ-isProp)

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Poset.Subset

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Downset

open import Cubical.AlgebraicGeometry.ZariskiLattice.Base
open import Cubical.AlgebraicGeometry.ZariskiLattice.UniversalProperty

open import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT


private variable ℓ : Level

module _ (R : CommRing ℓ) where
  open Iso
  open CommRingStr ⦃...⦄
  open PosetStr ⦃...⦄

  open Exponentiation R
  open CommIdeal R
  open RadicalIdeal R

  open ZarLat R
  open ZarLatUniversalProp R

  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice ZariskiLattice))
       using (IndPoset)

  private
    instance
      _ = R .snd
      _ = IndPoset .snd

    ⟨_⟩ : {n : ℕ} → FinVec (fst R) n → CommIdeal
    ⟨ V ⟩ = ⟨ V ⟩[ R ]

  unitLemmaZarLat : ∀ f → D f ≡ D 1r → f ∈ₚ R ˣ
  unitLemmaZarLat f Df≡D1 = containsOne→Unit  (1∈√→1∈ _ 1∈√⟨f⟩)
    where
    D1≤Df : D 1r ≤ D f
    D1≤Df = subst (_≤ D f) Df≡D1 (is-refl _)

    1∈√⟨f⟩ : 1r ∈ √ ⟨ replicateFinVec 1 f ⟩
    1∈√⟨f⟩ = √FGIdealCharLImpl _ _ (isEquivRel→effectiveIso ∼PropValued ∼EquivRel _ _ .fun D1≤Df .fst) zero


  module _ {n : ℕ} (f₁,⋯,fₙ : FinVec (fst R) n) where
    private
      D[f₁,⋯,fₙ] : ZL
      D[f₁,⋯,fₙ] = [ n , f₁,⋯,fₙ ]

    oneIdealLemmaZarLat :  D[f₁,⋯,fₙ] ≡ D 1r → 1r ∈ ⟨ f₁,⋯,fₙ ⟩
    oneIdealLemmaZarLat D[f₁,⋯,fₙ]≡D1 = 1∈√→1∈ _ 1∈√⟨f₁,⋯,fₙ⟩
      where
      D1≤D[f₁,⋯,fₙ] : D 1r ≤ D[f₁,⋯,fₙ]
      D1≤D[f₁,⋯,fₙ] = subst (_≤ D[f₁,⋯,fₙ]) D[f₁,⋯,fₙ]≡D1 (is-refl _)

      1∈√⟨f₁,⋯,fₙ⟩ : 1r ∈ √ ⟨ f₁,⋯,fₙ ⟩
      1∈√⟨f₁,⋯,fₙ⟩ = √FGIdealCharLImpl _ _
        (isEquivRel→effectiveIso ∼PropValued ∼EquivRel _ _ .fun D1≤D[f₁,⋯,fₙ] .fst) zero


module LocDownSetIso (R : CommRing ℓ) (f : R .fst) where
  open CommRingStr ⦃...⦄
  open DistLatticeStr ⦃...⦄
  open PosetStr ⦃...⦄

  open InvertingElementsBase R
  open UniversalProp f

  open ZarLat
  open ZarLatUniversalProp
  open IsSupport

  open DistLatticeDownset (ZariskiLattice R)
  open Order (DistLattice→Lattice (ZariskiLattice R))
  open LatticeTheory (DistLattice→Lattice (ZariskiLattice R))
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice (ZariskiLattice R)))
       using () renaming (IndPoset to ZLRPoset)

  open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice (ZariskiLattice R)))
       using (≤-∧LPres ; ∧≤RCancel)

  private
    instance
      _ = R .snd
      _ = ZariskiLattice R .snd
      _ = ZLRPoset .snd

    powerLemma : ∀ fⁿ → fⁿ ∈ₚ [ f ⁿ|n≥0] → D R f ∧l D R fⁿ ≡ D R f
    powerLemma fⁿ = PT.rec (squash/ _ _)
                      λ (n , fⁿ≡f^n) → cong (λ x → D R f ∧l D R x) fⁿ≡f^n
                                         ∙ ≤j→≤m _ _ (supportExpIneq (isSupportD R) n f)

    locEqPowerLemma : ∀ r fⁿ → fⁿ ∈ₚ [ f ⁿ|n≥0]
                    → D R f ∧l D R (r · fⁿ) ≡ D R f ∧l D R r
    locEqPowerLemma r fⁿ fⁿIsPow =
      D R f ∧l D R (r · fⁿ)      ≡⟨ cong (D R f ∧l_) (isSupportD R .·≡∧ _ _) ⟩
      D R f ∧l (D R r ∧l D R fⁿ) ≡⟨ ∧lAssoc (D R f) (D R r) (D R fⁿ) ⟩
      (D R f ∧l D R r) ∧l D R fⁿ ≡⟨ ∧l.commAssocr (D R f) (D R r) (D R fⁿ) ⟩
      (D R f ∧l D R fⁿ) ∧l D R r ≡⟨ cong (_∧l D R r) (powerLemma _ fⁿIsPow) ⟩
      D R f ∧l D R r ∎

    locEqPowerLemma2 : ∀ r fᵐ fⁿ → fᵐ ∈ₚ [ f ⁿ|n≥0] → fⁿ ∈ₚ [ f ⁿ|n≥0]
                    → D R f ∧l D R (fᵐ · r · fⁿ) ≡ D R f ∧l D R r
    locEqPowerLemma2 r fᵐ fⁿ fᵐIsPow fⁿIsPow =
      D R f ∧l D R (fᵐ · r · fⁿ) ≡⟨  locEqPowerLemma (fᵐ · r) fⁿ fⁿIsPow ⟩
      D R f ∧l D R (fᵐ · r)      ≡⟨ cong (D R f ∧l_) (isSupportD R .·≡∧ _ _) ⟩
      D R f ∧l (D R fᵐ ∧l D R r) ≡⟨ ∧lAssoc (D R f) (D R fᵐ) (D R r) ⟩
      (D R f ∧l D R fᵐ) ∧l D R r ≡⟨ cong (_∧l D R r) (powerLemma _ fᵐIsPow) ⟩
      D R f ∧l D R r ∎


  locDownSupp : R[1/ f ] → ↓ (D R f)
  locDownSupp =
    SQ.rec
      (isSetΣSndProp squash/ λ x → is-prop-valued x _)
        -- the actual map: r/fⁿ ↦ Dr∧Df
        (λ (r , _) → (D R f ∧l D R r) , ≤m→≤j _ _ (∧≤RCancel (D R f) (D R r)))
          -- coherence
          λ (r , fⁿ , fⁿIsPow) (r' , fᵐ , fᵐIsPow) ((fᵏ , fᵏIsPow) , fᵏrfᵐ≡fᵏr'fⁿ)
            → Σ≡Prop (λ x → is-prop-valued x _)
              (sym (locEqPowerLemma2 r fᵏ fᵐ fᵏIsPow fᵐIsPow)
              ∙∙ cong (λ x → D R f ∧l D R x) fᵏrfᵐ≡fᵏr'fⁿ
              ∙∙ locEqPowerLemma2 r' fᵏ fⁿ fᵏIsPow fⁿIsPow)

  isSupportLocDownSupp : IsSupport R[1/ f ]AsCommRing (↓ᴰᴸ (D R f)) locDownSupp
  pres0 isSupportLocDownSupp =
    Σ≡Prop (λ x → is-prop-valued x _)
           (cong (D R f ∧l_) (isSupportD R .pres0) ∙ 0lRightAnnihilates∧l (D R f))
  pres1 isSupportLocDownSupp = Σ≡Prop (λ x → is-prop-valued x _) (∧lRid (D R f))
  ·≡∧ isSupportLocDownSupp =
    SQ.elimProp2
      (λ _ _ → DistLatticeStr.is-set (↓ᴰᴸ (D R f) .snd) _ _)
        λ (r , _) (r' , _) → Σ≡Prop (λ x → is-prop-valued x _)
                               (cong (D R f ∧l_) (isSupportD R .·≡∧ r r')
                                 ∙ ∧lLdist∧l (D R f) (D R r) (D R r'))
  +≤∨ isSupportLocDownSupp =
    SQ.elimProp2
      (λ _ _ → DistLatticeStr.is-set (↓ᴰᴸ (D R f) .snd) _ _)
        λ (r , fⁿ , fⁿIsPow) (r' , fᵐ , fᵐIsPow)
          → Σ≡Prop (λ x → is-prop-valued x _)
                   (subst ((D R f ∧l D R ((r · fᵐ) + (r' · fⁿ))) ≤_)
                          (path r r' fⁿ fᵐ fⁿIsPow fᵐIsPow)
                          (ineq r r' fⁿ fᵐ))
    where
    ineq : ∀ r r' fⁿ fᵐ
         → (D R f ∧l D R (r · fᵐ + r' · fⁿ)) ≤ (D R f ∧l (D R (r · fᵐ) ∨l D R (r' · fⁿ)))
    ineq r r' fⁿ fᵐ = ≤m→≤j _ _ (≤-∧LPres (D R (r · fᵐ + r' · fⁿ))
                                          (D R (r · fᵐ) ∨l D R (r' · fⁿ))
                                          (D R f)
                                (≤j→≤m _ _ (isSupportD R .+≤∨ (r · fᵐ) (r' · fⁿ))))

    path : ∀ r r' fⁿ fᵐ → fⁿ ∈ₚ [ f ⁿ|n≥0] → fᵐ ∈ₚ [ f ⁿ|n≥0]
         → D R f ∧l (D R (r · fᵐ) ∨l D R (r' · fⁿ))
         ≡ (D R f ∧l D R r) ∨l (D R f ∧l D R r')
    path r r' fⁿ fᵐ fⁿIsPow fᵐIsPow =
      ∧lLdist∨l (D R f) (D R (r · fᵐ)) (D R (r' · fⁿ))
      ∙ cong₂ (_∨l_) (locEqPowerLemma r fᵐ fᵐIsPow) (locEqPowerLemma r' fⁿ fⁿIsPow)


  -- one direction of the equivalence
  locToDownHom : DistLatticeHom (ZariskiLattice R[1/ f ]AsCommRing) (↓ᴰᴸ (D R f))
  locToDownHom = ZLHasUniversalProp _ _ _ isSupportLocDownSupp .fst .fst

  toDownSupp : R .fst → ↓ (D R f)
  toDownSupp = locDownSupp ∘ _/1

  isSupportToDownSupp : IsSupport R (↓ᴰᴸ (D R f)) toDownSupp
  isSupportToDownSupp = presSupportPrecomp /1AsCommRingHom _ _ isSupportLocDownSupp

  -- the map ZL R → ZL R[1/f] → ↓Df is just Df∧_
  -- does not type check without lossy unification!!!
  toLocToDown≡ToDown : locToDownHom ∘dl inducedZarLatHom /1AsCommRingHom
                     ≡ toDownHom (D R f)
  toLocToDown≡ToDown =
    cong fst (isContr→isProp
      (ZLHasUniversalProp R (↓ᴰᴸ (D R f)) toDownSupp isSupportToDownSupp)
        (locToDownHom ∘dl (inducedZarLatHom /1AsCommRingHom) , toLocToDownComm)
        (toDownHom (D R f) , toDownComm))
    where
    toDownComm : toDownHom (D R f) .fst ∘ (D R) ≡ toDownSupp
    toDownComm = funExt λ r → Σ≡Prop (λ x → is-prop-valued x _) refl

    toLocToDownComm : locToDownHom .fst ∘ inducedZarLatHom /1AsCommRingHom .fst ∘ D R
                    ≡ toDownSupp
    toLocToDownComm =
        locToDownHom .fst ∘ (inducedZarLatHom /1AsCommRingHom) .fst ∘ D R

      ≡⟨ cong (locToDownHom .fst ∘_) (inducedZarLatHomComm /1AsCommRingHom) ⟩

        locToDownHom .fst ∘ D R[1/ f ]AsCommRing ∘ _/1

      ≡⟨ ∘-assoc (locToDownHom .fst) (D R[1/ f ]AsCommRing) _/1 ⟩

        (locToDownHom .fst ∘ D R[1/ f ]AsCommRing) ∘ _/1

      ≡⟨ cong (_∘ _/1) (ZLHasUniversalProp _ _ _ isSupportLocDownSupp .fst .snd) ⟩

        locDownSupp ∘ _/1 ∎
