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
                                         renaming ( _∈_ to _∈ₚ_ ; subst-∈ to subst-∈ₚ
                                                  ; ∈-isProp to ∈ₚ-isProp)

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
open import Cubical.Algebra.CommRing.Localisation.Limit
open import Cubical.Algebra.CommRing.Instances.Unit
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Properties
open import Cubical.Algebra.CommAlgebra.Localisation
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
open import Cubical.Categories.Limits.Terminal
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

 BasicOpens : ℙ ZL
 BasicOpens 𝔞 = (∃[ f ∈ R ] (D f ≡ 𝔞)) , isPropPropTrunc

 BO : Type ℓ
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

 BOCat : Category ℓ ℓ
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

    f∈√⟨g⟩ : f ∈ √ ⟨ g ⟩ₛ
    f∈√⟨g⟩ = isEquivRel→effectiveIso ∼PropValued ∼EquivRel _ _ .fun Df≤Dg .fst zero


 open PreSheafFromUniversalProp ZariskiCat P 𝓕 uniqueHom
 𝓞ᴮ : Functor (BOCat ^op) CommRingsCategory
 𝓞ᴮ = funcComp (ForgetfulCommAlgebra→CommRing R') universalPShf

 -- The extension
 open Functor
 open PreSheafExtension ZariskiLattice CommRingsCategory LimitsCommRingsCategory BasicOpens
 𝓞 : Functor (ZariskiCat ^op) CommRingsCategory
 𝓞 = DLRan 𝓞ᴮ

 toBasisPath : ∀ f → 𝓞 .F-ob (D f) ≡ 𝓞ᴮ .F-ob (D f , ∣ f , refl ∣₁)
 toBasisPath f = cong (λ F → F .F-ob (D f , ∣ f , refl ∣₁))
                      (NatIsoToPath isUnivalentCommRingsCategory (DLRanNatIso 𝓞ᴮ))


 open InvertingElementsBase R'
 private
   Forgetful = ForgetfulCommAlgebra→CommRing R' {ℓ' = ℓ}

   𝓞ᴮOb≡ : ∀ f → 𝓞ᴮ .F-ob (D f , ∣ f , refl ∣₁) ≡ R[1/ f ]AsCommRing
   𝓞ᴮOb≡ f = 𝓞ᴮ .F-ob (D f , ∣ f , refl ∣₁)     ≡⟨ refl ⟩
     -- all of this should hold by refl -----------------------------------------------------------
     -- but somehow Agda takes forever to type-check if you don't use -----------------------------
     -- the lemma funcCompOb≡ (which is just refl itself) or if you leave out ---------------------
     -- any of the intermediate refl steps --------------------------------------------------------
       (funcComp (ForgetfulCommAlgebra→CommRing R') universalPShf) .F-ob (D f , ∣ f , refl ∣₁)
     ≡⟨ funcCompOb≡ Forgetful universalPShf _ ⟩
       Forgetful .F-ob R[1/ f ]AsCommAlgebra
     ≡⟨ refl ⟩
     ----------------------------------------------------------------------------------------------
     CommAlgebra→CommRing R[1/ f ]AsCommAlgebra ≡⟨ invElCommAlgebra→CommRingPath f ⟩
     R[1/ f ]AsCommRing                         ∎

 baseSections : ∀ f → 𝓞 .F-ob (D f) ≡ R[1/ f ]AsCommRing
 baseSections f = toBasisPath f ∙ 𝓞ᴮOb≡ f

 globalSection : 𝓞 .F-ob (D 1r) ≡ R'
 globalSection = baseSections 1r ∙  invertingUnitsPath _ _ (Units.RˣContainsOne _)


 -- TODO: prove that 𝓞ᴮ is a sheaf!!!
 open SheafOnBasis ZariskiLattice (CommRingsCategory {ℓ = ℓ}) BasicOpens basicOpensAreBasis
 open DistLatticeStr ⦃...⦄
 private instance _ = snd ZariskiLattice

 isSheaf𝓞ᴮ : isDLBasisSheaf 𝓞ᴮ
 isSheaf𝓞ᴮ {n = zero} α isBO⋁α A cᴬ = uniqueExists
   (isTerminal𝓞ᴮ[0] A .fst)
     (λ {(sing ()) ; (pair () _ _) }) -- the unique morphism is a cone morphism
       (isPropIsConeMor _ _)
         λ φ _ → isTerminal𝓞ᴮ[0] A .snd φ
   where
   -- D(0) is not 0 of the Zariski  lattice by refl!
   p : 𝓞ᴮ .F-ob (0l , isBO⋁α) ≡ R[1/ 0r ]AsCommRing
   p = 𝓞ᴮ .F-ob (0l , isBO⋁α)
     ≡⟨ cong (𝓞ᴮ .F-ob) (Σ≡Prop (λ _ → ∈ₚ-isProp _ _)
             (eq/ _ _ ((λ ()) , λ {zero → ∣ 1 , ∣ (λ ()) , 0LeftAnnihilates _ ∣₁ ∣₁ }))) ⟩
       𝓞ᴮ .F-ob (D 0r , ∣ 0r , refl ∣₁)
     ≡⟨ 𝓞ᴮOb≡ 0r ⟩
       R[1/ 0r ]AsCommRing ∎

   isTerminal𝓞ᴮ[0] : isTerminal CommRingsCategory (𝓞ᴮ .F-ob (0l , isBO⋁α))
   isTerminal𝓞ᴮ[0] = subst (isTerminal CommRingsCategory)
                           (sym (p ∙ R[1/0]≡0)) (TerminalCommRing .snd)

 isSheaf𝓞ᴮ {n = suc n} = {!!}

 -- our main result
 isSheaf𝓞 : isDLSheaf _ _ 𝓞
 isSheaf𝓞 = isDLSheafDLRan _ _ isSheaf𝓞ᴮ
