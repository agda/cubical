{-

   This module defines the basic opens of the Zariski lattice and proves that they're a basis of the lattice.
   It also contains the construction of the structure presheaf and a proof of the sheaf property on basic opens,
   using the theory developed in the module PreSheafFromUniversalProp and its toSheaf.lemma.
   Note that the structure sheaf is a functor into R-algebras and not just commutative rings.

-}

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
open import Cubical.Data.Bool
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
open import Cubical.Algebra.RingSolver.Reflection
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis
open import Cubical.Algebra.DistLattice.BigOps
open import Cubical.Algebra.ZariskiLattice.Base
open import Cubical.Algebra.ZariskiLattice.UniversalProperty

open import Cubical.Categories.Category.Base hiding (_[_,_])
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Instances.CommAlgebras
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.Semilattice
open import Cubical.Categories.DistLatticeSheaf

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso
open BinaryRelation
open isEquivRel

private
  variable
    ℓ ℓ' : Level



module _ (R' : CommRing ℓ) where
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
  ⟨_⟩ : R → CommIdeal
  ⟨ f ⟩ = ⟨ replicateFinVec 1 f ⟩[ R' ]
  ⟨_⟩ₚ : R × R → CommIdeal -- p is for pair
  ⟨ f , g ⟩ₚ = ⟨ replicateFinVec 1 f ++Fin replicateFinVec 1 g ⟩[ R' ]


 BasicOpens : ℙ ZL
 BasicOpens 𝔞 = (∃[ f ∈ R ] (D f ≡ 𝔞)) , isPropPropTrunc

 BO : Type (ℓ-suc ℓ)
 BO = Σ[ 𝔞 ∈ ZL ] (𝔞 ∈ₚ BasicOpens)

 basicOpensAreBasis : IsBasis ZariskiLattice BasicOpens
 contains1 basicOpensAreBasis = ∣ 1r , isZarMapD .pres1 ∣
 ∧lClosed basicOpensAreBasis 𝔞 𝔟 = map2
            λ (f , Df≡𝔞) (g , Dg≡𝔟) → (f · g) , isZarMapD .·≡∧ f g ∙ cong₂ (_∧z_) Df≡𝔞 Dg≡𝔟
 ⋁Basis basicOpensAreBasis = elimProp (λ _ → isPropPropTrunc) Σhelper
  where
  Σhelper : (a : Σ[ n ∈ ℕ ] FinVec R n)
          → ∃[ n ∈ ℕ ] Σ[ α ∈ FinVec ZL n ] (∀ i → α i ∈ₚ BasicOpens) × (⋁ α ≡ [ a ])
  Σhelper (n , α) = ∣ n , (D ∘ α) , (λ i → ∣ α i , refl ∣) , path ∣
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
       (sym (·Rid (s /1))) --can't apply the lemma directly as we get mult with 1 somewhere
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

    radicalHelper : √ ⟨ f , g ⟩ₚ ≡ √ ⟨ g ⟩
    radicalHelper =
      isEquivRel→effectiveIso (λ _ _ → isSetCommIdeal _ _) ∼EquivRel _ _ .fun Df≤Dg

    f∈√⟨g⟩ : f ∈ √ ⟨ g ⟩
    f∈√⟨g⟩ = subst (f ∈_) radicalHelper (∈→∈√ _ _ (indInIdeal _ _ zero))


 open PreSheafFromUniversalProp ZariskiCat P 𝓕 uniqueHom
 BasisStructurePShf : Functor (BOCat ^op) (CommAlgebrasCategory R')
 BasisStructurePShf = universalPShf


 -- now prove the sheaf properties
 open SheafOnBasis ZariskiLattice (CommAlgebrasCategory R' {ℓ' = ℓ})
                   (TerminalCommAlgebra R') BasicOpens basicOpensAreBasis

 isSheafBasisStructurePShf : isDLBasisSheaf BasisStructurePShf
 fst isSheafBasisStructurePShf 0∈BO =
   transport (λ i → F-ob (0z , canonical0∈BO≡0∈BO i) ≡ UnitCommAlgebra R') R[1/0]≡0
   where
   open Functor ⦃...⦄
   instance
    _ = BasisStructurePShf

   canonical0∈BO : 0z ∈ₚ BasicOpens
   canonical0∈BO = ∣ 0r , isZarMapD .pres0 ∣

   canonical0∈BO≡0∈BO : canonical0∈BO ≡ 0∈BO
   canonical0∈BO≡0∈BO = BasicOpens 0z .snd _ _

   R[1/0]≡0 : R[1/ 0r ]AsCommAlgebra ≡ UnitCommAlgebra R'
   R[1/0]≡0 = uaCommAlgebra (e , eIsRHom)
    where
    open InvertingElementsBase R' using (isContrR[1/0])
    open IsAlgebraHom

    e : R[1/ 0r ]AsCommAlgebra .fst ≃ UnitCommAlgebra R' .fst
    e = isContr→Equiv isContrR[1/0] isContrUnit*

    eIsRHom : IsCommAlgebraEquiv (R[1/ 0r ]AsCommAlgebra .snd) e (UnitCommAlgebra R' .snd)
    pres0 eIsRHom = refl
    pres1 eIsRHom = refl
    pres+ eIsRHom _ _ = refl
    pres· eIsRHom _ _ = refl
    pres- eIsRHom _ = refl
    pres⋆ eIsRHom _ _ = refl

 snd isSheafBasisStructurePShf (𝔞 , 𝔞∈BO) (𝔟 , 𝔟∈BO) 𝔞∨𝔟∈BO = curriedHelper 𝔞 𝔟 𝔞∈BO 𝔟∈BO 𝔞∨𝔟∈BO
  where
  open condSquare
  {-
     here:
     BFsq (𝔞 , 𝔞∈BO) (𝔟 , 𝔟∈BO) 𝔞∨𝔟∈BO BasisStructurePShf =

     𝓞 (𝔞∨𝔟) → 𝓞 (𝔞)

       ↓         ↓

     𝓞 (𝔟)  →  𝓞 (𝔞∧𝔟)

  -}
  curriedHelper : (𝔞 𝔟 : ZL) (𝔞∈BO : 𝔞 ∈ₚ BasicOpens) (𝔟∈BO : 𝔟 ∈ₚ BasicOpens)
                  (𝔞∨𝔟∈BO : 𝔞 ∨z 𝔟 ∈ₚ BasicOpens)
                → isPullback (CommAlgebrasCategory R') _ _ _
                             (BFsq (𝔞 , 𝔞∈BO) (𝔟 , 𝔟∈BO) 𝔞∨𝔟∈BO BasisStructurePShf)
  curriedHelper 𝔞 𝔟 = elim3 (λ 𝔞∈BO 𝔟∈BO 𝔞∨𝔟∈BO → isPropIsPullback _ _ _ _
                            (BFsq (𝔞 , 𝔞∈BO) (𝔟 , 𝔟∈BO) 𝔞∨𝔟∈BO BasisStructurePShf))
                            Σhelper
   where
   -- write everything explicitly so things can type-check
   thePShfCospan : (a : Σ[ f ∈ R ] D f ≡ 𝔞) (b : Σ[ g ∈ R ] D g ≡ 𝔟)
                 → Cospan (CommAlgebrasCategory R')
   Cospan.l (thePShfCospan (f , Df≡𝔞) (g , Dg≡𝔟)) = BasisStructurePShf .Functor.F-ob (𝔟 , ∣ g , Dg≡𝔟 ∣)
   Cospan.m (thePShfCospan (f , Df≡𝔞) (g , Dg≡𝔟)) = BasisStructurePShf .Functor.F-ob
            (𝔞 ∧z 𝔟 , basicOpensAreBasis .∧lClosed 𝔞 𝔟 ∣ f , Df≡𝔞 ∣ ∣ g , Dg≡𝔟 ∣)
   Cospan.r (thePShfCospan (f , Df≡𝔞) (g , Dg≡𝔟)) = BasisStructurePShf .Functor.F-ob (𝔞 , ∣ f , Df≡𝔞 ∣)
   Cospan.s₁ (thePShfCospan (f , Df≡𝔞) (g , Dg≡𝔟)) = BasisStructurePShf .Functor.F-hom
             {x = (𝔟 , ∣ g , Dg≡𝔟 ∣)}
             {y = (𝔞 ∧z 𝔟 , basicOpensAreBasis .∧lClosed 𝔞 𝔟 ∣ f , Df≡𝔞 ∣ ∣ g , Dg≡𝔟 ∣)}
             (hom-∧₂  ZariskiLattice (CommAlgebrasCategory R' {ℓ' = ℓ}) (TerminalCommAlgebra R') 𝔞 𝔟)
   Cospan.s₂ (thePShfCospan (f , Df≡𝔞) (g , Dg≡𝔟)) = BasisStructurePShf .Functor.F-hom
             {x = (𝔞 , ∣ f , Df≡𝔞 ∣)}
             {y = (𝔞 ∧z 𝔟 , basicOpensAreBasis .∧lClosed 𝔞 𝔟 ∣ f , Df≡𝔞 ∣ ∣ g , Dg≡𝔟 ∣)}
             (hom-∧₁  ZariskiLattice (CommAlgebrasCategory R' {ℓ' = ℓ}) (TerminalCommAlgebra R') 𝔞 𝔟)


   Σhelper : (a : Σ[ f ∈ R ] D f ≡ 𝔞) (b : Σ[ g ∈ R ] D g ≡ 𝔟) (c : Σ[ h ∈ R ] D h ≡ 𝔞 ∨z 𝔟)
           → isPullback (CommAlgebrasCategory R') (thePShfCospan a b) _ _
                        (BFsq (𝔞 , ∣ a ∣) (𝔟 , ∣ b ∣) ∣ c ∣ BasisStructurePShf)
   Σhelper (f , Df≡𝔞) (g , Dg≡𝔟) (h , Dh≡𝔞∨𝔟) = toSheaf.lemma
           (𝔞 ∨z 𝔟 , ∣ h , Dh≡𝔞∨𝔟 ∣)
           (𝔞 , ∣ f , Df≡𝔞 ∣)
           (𝔟 , ∣ g , Dg≡𝔟 ∣)
           (𝔞 ∧z 𝔟 , basicOpensAreBasis .∧lClosed 𝔞 𝔟 ∣ f , Df≡𝔞 ∣ ∣ g , Dg≡𝔟 ∣)
           (Bsq (𝔞 , ∣ f , Df≡𝔞 ∣) (𝔟 , ∣ g , Dg≡𝔟 ∣) ∣ h , Dh≡𝔞∨𝔟 ∣)
           theAlgebraCospan theAlgebraPullback refl gPath fPath fgPath
    where
    open Exponentiation R'
    open RadicalIdeal R'
    open InvertingElementsBase R'
    open DoubleLoc R' h
    open S⁻¹RUniversalProp R' [ h ⁿ|n≥0] (powersFormMultClosedSubset h)
    open CommIdeal R[1/ h ]AsCommRing using () renaming (CommIdeal to CommIdealₕ ; _∈_ to _∈ₕ_)

    instance
     _ = snd R[1/ h ]AsCommRing

    ⟨_⟩ₕ : R[1/ h ] × R[1/ h ] → CommIdealₕ
    ⟨ x , y ⟩ₕ = ⟨ replicateFinVec 1 x ++Fin replicateFinVec 1 y ⟩[ R[1/ h ]AsCommRing ]

    -- the crucial algebraic fact:
    radicalPath : √ ⟨ h ⟩ ≡ √ ⟨ f , g ⟩ₚ
    radicalPath = isEquivRel→effectiveIso (λ _ _ → isSetCommIdeal _ _) ∼EquivRel _ _ .fun DHelper
     where
     DHelper : D h ≡ D f ∨z D g
     DHelper = Dh≡𝔞∨𝔟 ∙ cong₂ (_∨z_) (sym Df≡𝔞) (sym Dg≡𝔟)

    f∈√⟨h⟩ : f ∈ √ ⟨ h ⟩
    f∈√⟨h⟩ = subst (f ∈_) (sym radicalPath) (∈→∈√ _ _ (indInIdeal _ _ zero))

    g∈√⟨h⟩ : g ∈ √ ⟨ h ⟩
    g∈√⟨h⟩ = subst (g ∈_) (sym radicalPath) (∈→∈√ _ _ (indInIdeal _ _ (suc zero)))

    fg∈√⟨h⟩ : (f · g) ∈ √ ⟨ h ⟩
    fg∈√⟨h⟩ = √ ⟨ h ⟩ .snd .·Closed f g∈√⟨h⟩

    1∈fgIdeal : 1r ∈ₕ ⟨ (f /1) , (g /1) ⟩ₕ
    1∈fgIdeal = helper1 (subst (h ∈_) radicalPath (∈→∈√ _ _ (indInIdeal _ _ zero)))
     where
     helper1 : h ∈ √ ⟨ f , g ⟩ₚ
             → 1r ∈ₕ ⟨ (f /1) , (g /1) ⟩ₕ
     helper1 = PT.rec isPropPropTrunc (uncurry helper2)
      where
      helper2 : (n : ℕ)
              → h ^ n ∈ ⟨ f , g ⟩ₚ
              → 1r ∈ₕ ⟨ (f /1) , (g /1) ⟩ₕ
      helper2 n = map helper3
       where
       helper3 : Σ[ α ∈ FinVec R 2 ]
                  h ^ n ≡ linearCombination R' α (λ { zero → f ; (suc zero) → g })
               → Σ[ β ∈ FinVec R[1/ h ] 2 ]
                  1r ≡ linearCombination R[1/ h ]AsCommRing β
                                         λ { zero → f /1 ; (suc zero) → g /1 }
       helper3 (α , p) = β , path
        where
        β : FinVec R[1/ h ] 2
        β zero = [ α zero , h ^ n , ∣ n , refl ∣ ]
        β (suc zero) = [ α (suc zero) , h ^ n , ∣ n , refl ∣ ]

        path : 1r ≡ linearCombination R[1/ h ]AsCommRing β
                                      λ { zero → f /1 ; (suc zero) → g /1 }
        path = eq/ _ _ ((1r , ∣ 0 , refl ∣) , bigPath)
             ∙ cong (β zero · (f /1) +_) (sym (+Rid (β (suc zero) · (g /1))))
         where
         useSolver1 : ∀ hn → 1r · 1r · ((hn · 1r) · (hn · 1r)) ≡ hn · hn
         useSolver1 = solve R'

         useSolver2 : ∀ az f hn as g → hn · (az · f + (as · g + 0r))
                                      ≡ 1r · (az · f · (hn · 1r) + as · g · (hn · 1r)) · 1r
         useSolver2 = solve R'

         bigPath : 1r · 1r · ((h ^ n · 1r) · (h ^ n · 1r))
                 ≡ 1r · (α zero · f · (h ^ n · 1r) + α (suc zero) · g · (h ^ n · 1r)) · 1r
         bigPath = useSolver1 (h ^ n) ∙ cong (h ^ n ·_) p ∙ useSolver2 _ _ _ _ _

    {-

      We get the following pullback square in CommRings

        R[1/h]   →    R[1/h][1/f]
              ⌟
        ↓             ↓

        R[1/h][1/g] → R[1/h][1/fg]

      this lifts to a pullback in R-Algebras using PullbackFromCommRing
      as all for rings have canonical morphisms coming from R
      and all the triangles commute.

      Then using toSheaf.lemma we get the desired square

        R[1/h]  →  R[1/f]
              ⌟
        ↓          ↓

        R[1/g]  →  R[1/fg]

      by only providing paths between the corresponding vertices of the square.
      These paths are constructed using S⁻¹RAlgCharEquiv, which gives
      an equivalent characterization of the universal property of localization
      that can be found in e.g. Cor 3.2 of Atiyah-MacDonald

    -}

    theRingCospan = fgCospan R[1/ h ]AsCommRing (f /1) (g /1)
    theRingPullback = fgPullback R[1/ h ]AsCommRing (f /1) (g /1) 1∈fgIdeal

    R[1/h][1/f] = InvertingElementsBase.R[1/_] R[1/ h ]AsCommRing (f /1)
    R[1/h][1/f]AsCommRing = InvertingElementsBase.R[1/_]AsCommRing R[1/ h ]AsCommRing (f /1)
    R[1/h][1/g] = InvertingElementsBase.R[1/_] R[1/ h ]AsCommRing (g /1)
    R[1/h][1/g]AsCommRing = InvertingElementsBase.R[1/_]AsCommRing R[1/ h ]AsCommRing (g /1)
    R[1/h][1/fg] = InvertingElementsBase.R[1/_] R[1/ h ]AsCommRing ((f /1) · (g /1))
    R[1/h][1/fg]AsCommRing = InvertingElementsBase.R[1/_]AsCommRing
                               R[1/ h ]AsCommRing ((f /1) · (g /1))

    open IsRingHom
    /1/1AsCommRingHomFG : CommRingHom R' R[1/h][1/fg]AsCommRing
    fst /1/1AsCommRingHomFG r = [ [ r , 1r , ∣ 0 , refl ∣ ] , 1r , ∣ 0 , refl ∣ ]
    pres0 (snd /1/1AsCommRingHomFG) = refl
    pres1 (snd /1/1AsCommRingHomFG) = refl
    pres+ (snd /1/1AsCommRingHomFG) x y = cong [_] (≡-× (cong [_] (≡-×
                                         (cong₂ _+_ (useSolver x) (useSolver y))
                                         (Σ≡Prop (λ _ → isPropPropTrunc) (useSolver 1r))))
                                         (Σ≡Prop (λ _ → isPropPropTrunc) (sym (·Rid 1r))))
      where
      useSolver : ∀ a → a ≡ a · 1r · (1r · 1r)
      useSolver = solve R'
    pres· (snd /1/1AsCommRingHomFG) x y = cong [_] (≡-× (cong [_] (≡-× refl
                                            (Σ≡Prop (λ _ → isPropPropTrunc) (sym (·Rid 1r)))))
                                            (Σ≡Prop (λ _ → isPropPropTrunc) (sym (·Rid 1r))))
    pres- (snd /1/1AsCommRingHomFG) x = refl

    open Cospan
    open Pullback
    open RingHoms
    isRHomR[1/h]→R[1/h][1/f] : theRingPullback .pbPr₂ ∘r /1AsCommRingHom ≡ /1/1AsCommRingHom f
    isRHomR[1/h]→R[1/h][1/f] = RingHom≡ (funExt (λ x → refl))

    isRHomR[1/h]→R[1/h][1/g] : theRingPullback .pbPr₁ ∘r /1AsCommRingHom ≡ /1/1AsCommRingHom g
    isRHomR[1/h]→R[1/h][1/g] = RingHom≡ (funExt (λ x → refl))

    isRHomR[1/h][1/f]→R[1/h][1/fg] : theRingCospan .s₂ ∘r /1/1AsCommRingHom f ≡ /1/1AsCommRingHomFG
    isRHomR[1/h][1/f]→R[1/h][1/fg] = RingHom≡ (funExt
      (λ x → cong [_] (≡-× (cong [_] (≡-× (cong (x ·_) (transportRefl 1r) ∙ ·Rid x)
          (Σ≡Prop (λ _ → isPropPropTrunc) (cong (1r ·_) (transportRefl 1r) ∙ ·Rid 1r))))
          (Σ≡Prop (λ _ → isPropPropTrunc) (cong (1r ·_) (transportRefl 1r) ∙ ·Rid 1r)))))

    isRHomR[1/h][1/g]→R[1/h][1/fg] : theRingCospan .s₁ ∘r /1/1AsCommRingHom g ≡ /1/1AsCommRingHomFG
    isRHomR[1/h][1/g]→R[1/h][1/fg] = RingHom≡ (funExt
      (λ x → cong [_] (≡-× (cong [_] (≡-× (cong (x ·_) (transportRefl 1r) ∙ ·Rid x)
          (Σ≡Prop (λ _ → isPropPropTrunc) (cong (1r ·_) (transportRefl 1r) ∙ ·Rid 1r))))
          (Σ≡Prop (λ _ → isPropPropTrunc) (cong (1r ·_) (transportRefl 1r) ∙ ·Rid 1r)))))


    open PullbackFromCommRing R' theRingCospan theRingPullback
         /1AsCommRingHom (/1/1AsCommRingHom f) (/1/1AsCommRingHom g) /1/1AsCommRingHomFG
    theAlgebraCospan = algCospan isRHomR[1/h]→R[1/h][1/f]
                                 isRHomR[1/h]→R[1/h][1/g]
                                 isRHomR[1/h][1/f]→R[1/h][1/fg]
                                 isRHomR[1/h][1/g]→R[1/h][1/fg]
    theAlgebraPullback = algPullback isRHomR[1/h]→R[1/h][1/f]
                                     isRHomR[1/h]→R[1/h][1/g]
                                     isRHomR[1/h][1/f]→R[1/h][1/fg]
                                     isRHomR[1/h][1/g]→R[1/h][1/fg]

    --and the three remaining paths
    fPath : theAlgebraCospan .r ≡ R[1/ f ]AsCommAlgebra
    fPath = doubleLocCancel f∈√⟨h⟩
     where
     open DoubleAlgLoc R' h f

    gPath : theAlgebraCospan .l ≡ R[1/ g ]AsCommAlgebra
    gPath = doubleLocCancel g∈√⟨h⟩
     where
     open DoubleAlgLoc R' h g

    fgPath : theAlgebraCospan .m ≡ R[1/ (f · g) ]AsCommAlgebra
    fgPath = path ∙ doubleLocCancel fg∈√⟨h⟩
     where
     open DoubleAlgLoc R' h (f · g)
     open CommAlgChar R'

     R[1/h][1/fg]AsCommRing' = InvertingElementsBase.R[1/_]AsCommRing R[1/ h ]AsCommRing ((f · g) /1)

     path : toCommAlg (R[1/h][1/fg]AsCommRing , /1/1AsCommRingHomFG)
          ≡ toCommAlg (R[1/h][1/fg]AsCommRing' , /1/1AsCommRingHom (f · g))
     path = cong toCommAlg (ΣPathP (p , q))
      where
      eqInR[1/h] : (f /1) · (g /1) ≡ (f · g) /1
      eqInR[1/h] = sym (/1AsCommRingHom .snd .pres· f g)

      p : R[1/h][1/fg]AsCommRing ≡ R[1/h][1/fg]AsCommRing'
      p i = InvertingElementsBase.R[1/_]AsCommRing R[1/ h ]AsCommRing (eqInR[1/h] i)

      q : PathP (λ i → CommRingHom R' (p i)) /1/1AsCommRingHomFG (/1/1AsCommRingHom (f · g))
      q = toPathP (RingHom≡ (funExt (
            λ x → cong [_] (≡-× (cong [_] (≡-× (transportRefl _ ∙ transportRefl x)
                (Σ≡Prop (λ _ → isPropPropTrunc) (transportRefl 1r))))
                (Σ≡Prop (λ _ → isPropPropTrunc) (transportRefl 1r))))))
