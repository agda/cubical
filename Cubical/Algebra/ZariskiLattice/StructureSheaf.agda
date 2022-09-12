{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.ZariskiLattice.StructureSheaf where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset using (ℙ ; ⊆-refl-consequence)
                                         renaming (_∈_ to _∈ₚ_ ; subst-∈ to subst-∈ₚ)

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm
                                      ; ·-identityʳ to ·ℕ-rid)
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Algebra.CommRing.Localisation.UniversalProperty
open import Cubical.Algebra.CommRing.Localisation.InvertingElements
open import Cubical.Algebra.CommRing.Localisation.PullbackSquare
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Properties
open import Cubical.Algebra.CommAlgebra.Localisation
open import Cubical.Algebra.CommAlgebra.Instances.Unit
open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis
open import Cubical.Algebra.DistLattice.BigOps
open import Cubical.Algebra.ZariskiLattice.Base
open import Cubical.Algebra.ZariskiLattice.UniversalProperty

open import Cubical.Categories.Category.Base hiding (_[_,_])
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Limits.RightKan

open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.CommAlgebras
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.Semilattice

open import Cubical.Categories.DistLatticeSheaf.Diagram
open import Cubical.Categories.DistLatticeSheaf.Base
open import Cubical.Categories.DistLatticeSheaf.Extension

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso
open BinaryRelation
open isEquivRel


module _ {ℓ : Level} (R' : CommRing ℓ) where
 open CommRingStr ⦃...⦄
 open RingTheory (CommRing→Ring R')
 open CommIdeal R'
 open isCommIdeal

 open ZarLat R'
 open ZarLatUniversalProp R'
 open IsZarMap

 open Join ZariskiLattice
 open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice ZariskiLattice))
 open IsBasis

 private
  R = fst R'
  instance
   _ = snd R'
  ⟨_⟩ₛ : R → CommIdeal -- s is for singleton
  ⟨ f ⟩ₛ = ⟨ replicateFinVec 1 f ⟩[ R' ]
  ⟨_⟩ₚ : R × R → CommIdeal -- p is for pair
  ⟨ f , g ⟩ₚ = ⟨ replicateFinVec 1 f ++Fin replicateFinVec 1 g ⟩[ R' ]


 BasicOpens : ℙ ZL
 BasicOpens 𝔞 = (∃[ f ∈ R ] (D f ≡ 𝔞)) , isPropPropTrunc

 BO : Type (ℓ-suc ℓ)
 BO = Σ[ 𝔞 ∈ ZL ] (𝔞 ∈ₚ BasicOpens)

 basicOpensAreBasis : IsBasis ZariskiLattice BasicOpens
 contains1 basicOpensAreBasis = ∣ 1r , isZarMapD .pres1 ∣₁
 ∧lClosed basicOpensAreBasis 𝔞 𝔟 = map2
            λ (f , Df≡𝔞) (g , Dg≡𝔟) → (f · g) , isZarMapD .·≡∧ f g ∙ cong₂ (_∧z_) Df≡𝔞 Dg≡𝔟
 ⋁Basis basicOpensAreBasis = elimProp (λ _ → isPropPropTrunc) Σhelper
  where
  Σhelper : (a : Σ[ n ∈ ℕ ] FinVec R n)
          → ∃[ n ∈ ℕ ] Σ[ α ∈ FinVec ZL n ] (∀ i → α i ∈ₚ BasicOpens) × (⋁ α ≡ [ a ])
  Σhelper (n , α) = ∣ n , (D ∘ α) , (λ i → ∣ α i , refl ∣₁) , path ∣₁
   where
   path : ⋁ (D ∘ α) ≡ [ n , α ]
   path = funExt⁻ (cong fst ZLUniversalPropCorollary) _


 -- The structure presheaf on BO
 ZariskiCat = DistLatticeCategory ZariskiLattice

 BOCat : Category (ℓ-suc ℓ) (ℓ-suc ℓ)
 BOCat = ΣPropCat ZariskiCat BasicOpens

 private
  P : ZL → Type _
  P 𝔞 = Σ[ f ∈ R ] (D f ≡ 𝔞) -- the untruncated defining property

  𝓕 : Σ ZL P → CommAlgebra R' _
  𝓕 (_ , f , _) = R[1/ f ]AsCommAlgebra -- D(f) ↦ R[1/f]

  uniqueHom : ∀ (x y : Σ ZL P) → (fst x) ≤ (fst y) → isContr (CommAlgebraHom (𝓕 y) (𝓕 x))
  uniqueHom (𝔞 , f , p) (𝔟 , g , q) = contrHoms 𝔞 𝔟 f g p q
   where
   open InvertingElementsBase R'

   contrHoms : (𝔞 𝔟 : ZL) (f g : R) (p : D f ≡ 𝔞) (q : D g ≡ 𝔟)
             → 𝔞 ≤ 𝔟 → isContr (CommAlgebraHom R[1/ g ]AsCommAlgebra R[1/ f ]AsCommAlgebra)
   contrHoms 𝔞 𝔟 f g p q 𝔞≤𝔟 = R[1/g]HasAlgUniversalProp R[1/ f ]AsCommAlgebra
     λ s s∈[gⁿ|n≥0] → subst-∈ₚ (R[1/ f ]AsCommRing ˣ)
       (sym (·IdR (s /1))) --can't apply the lemma directly as we get mult with 1 somewhere
         (RadicalLemma.toUnit R' f g f∈√⟨g⟩ s s∈[gⁿ|n≥0])
    where
    open AlgLoc R' [ g ⁿ|n≥0] (powersFormMultClosedSubset g)
         renaming (S⁻¹RHasAlgUniversalProp to R[1/g]HasAlgUniversalProp)
    open S⁻¹RUniversalProp R' [ f ⁿ|n≥0] (powersFormMultClosedSubset f) using (_/1)
    open RadicalIdeal R'

    private
     instance
      _ = snd R[1/ f ]AsCommRing

    Df≤Dg : D f ≤ D g
    Df≤Dg = subst2 _≤_ (sym p) (sym q) 𝔞≤𝔟

    radicalHelper : √ ⟨ f , g ⟩ₚ ≡ √ ⟨ g ⟩ₛ
    radicalHelper =
      isEquivRel→effectiveIso (λ _ _ → isSetCommIdeal _ _) ∼EquivRel _ _ .fun Df≤Dg

    f∈√⟨g⟩ : f ∈ √ ⟨ g ⟩ₛ
    f∈√⟨g⟩ = subst (f ∈_) radicalHelper (∈→∈√ _ _ (indInIdeal _ _ zero))


 open PreSheafFromUniversalProp ZariskiCat P 𝓕 uniqueHom
 𝓞ᴮ : Functor (BOCat ^op) CommRingsCategory
 𝓞ᴮ = funcComp (ForgetfulCommAlgebra→CommRing R') universalPShf

 open Functor
 open DistLatticeStr ⦃...⦄
 private instance _ = (snd ZariskiLattice)
 abstract
   foo : ∀ f → universalPShf .F-ob (D f , ∣ f , refl ∣₁) ≡ R[1/ f ]AsCommAlgebra
   foo f = refl

 -- TODO: prove that 𝓞ᴮ is a sheaf!!!

 -- The extension
 module _ (commRingLimits : Limits CommRingsCategory) where
  -- should be LimitsCommRingsCategory but then need SmallZarLat here!!!
  open PreSheafExtension {ℓ'' = ℓ} ZariskiLattice CommRingsCategory commRingLimits BasicOpens
  𝓞 : Functor (ZariskiCat ^op) (CommRingsCategory {ℓ = ℓ})
  𝓞 = DLRan 𝓞ᴮ

  toBasisPath : ∀ f → 𝓞 .F-ob (D f) ≡ 𝓞ᴮ .F-ob (D f , ∣ f , refl ∣₁)
  toBasisPath f = cong (λ F → F .F-ob (D f , ∣ f , refl ∣₁))
                       (NatIsoToPath isUnivalentCommRingsCategory (DLRanNatIso 𝓞ᴮ))


  open InvertingElementsBase R'
  globalSections : 𝓞 .F-ob (D 1r) ≡ R'
  globalSections =
    𝓞 .F-ob 1l                                  ≡⟨ toBasisPath 1r ⟩
    𝓞ᴮ .F-ob (1l , ∣ 1r , refl ∣₁)             ≡⟨ refl ⟩
    (funcComp (ForgetfulCommAlgebra→CommRing R') universalPShf) .F-ob (1l , ∣ 1r , refl ∣₁)          ≡⟨ funcCompOb≡ (ForgetfulCommAlgebra→CommRing R') universalPShf _ ⟩
    (ForgetfulCommAlgebra→CommRing R') .F-ob (universalPShf .F-ob (1l , ∣ 1r , refl ∣₁))             ≡⟨ refl ⟩
    -- does not compute by refl, even though foo does
    ForgetfulCommAlgebra→CommRing R' {ℓ' = ℓ} .F-ob R[1/ 1r ]AsCommAlgebra ≡⟨ refl ⟩
    CommAlgebra→CommRing R[1/ 1r ]AsCommAlgebra ≡⟨ invElCommAlgebra→CommRingPath 1r ⟩
    R[1/ 1r ]AsCommRing                         ≡⟨ invertingUnitsPath _ _ (Units.RˣContainsOne _) ⟩
    R' ∎
