{-

   This module defines the basic opens of the Zariski lattice and proves that they're a basis of the lattice.
   It also contains the construction of the structure presheaf and a proof of the sheaf property on basic opens,
   using the theory developed in the module PreSheafFromUniversalProp and its toSheaf.lemma.
   Note that the structure sheaf is a functor into R-algebras and not just commutative rings.

-}

{-# OPTIONS --safe --lossy-unification #-}
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
open import Cubical.Relation.Binary.Order.Poset

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Algebra.CommRing.Localisation
open import Cubical.Algebra.CommRing.Instances.Unit
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Properties
open import Cubical.Algebra.CommAlgebra.Localisation
open import Cubical.Tactics.CommRingSolver
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
  Σhelper (n , α) = ∣ n , (D ∘ α) , (λ i → ∣ α i , refl ∣₁) , ⋁D≡ α ∣₁

 -- important fact that D(f)≤D(g) → isContr (R-Hom R[1/f] R[1/g])
 module _ where
   open InvertingElementsBase R'

   contrHoms : (f g : R)
             → D f ≤ D g
             → isContr (CommAlgebraHom R[1/ g ]AsCommAlgebra R[1/ f ]AsCommAlgebra)
   contrHoms f g Df≤Dg = R[1/g]HasAlgUniversalProp R[1/ f ]AsCommAlgebra
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

    f∈√⟨g⟩ : f ∈ √ ⟨ g ⟩ₛ
    f∈√⟨g⟩ = isEquivRel→effectiveIso ∼PropValued ∼EquivRel _ _ .fun Df≤Dg .fst zero


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
  uniqueHom (𝔞 , f , p) (𝔟 , g , q) 𝔞≤𝔟 = contrHoms f g Df≤Dg
    where
    Df≤Dg : D f ≤ D g
    Df≤Dg = subst2 _≤_ (sym p) (sym q) 𝔞≤𝔟



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


 open SheafOnBasis ZariskiLattice (CommRingsCategory {ℓ = ℓ}) BasicOpens basicOpensAreBasis
 open DistLatticeStr ⦃...⦄
 private instance _ = snd ZariskiLattice

 isSheaf𝓞ᴮ : isDLBasisSheaf 𝓞ᴮ
 isSheaf𝓞ᴮ {n = n} α = curriedHelper (fst ∘ α) (snd ∘ α)
  where
  curriedHelper : (𝔞 : FinVec ZL n) (𝔞∈BO : ∀ i → 𝔞 i ∈ₚ BasicOpens)
                  (⋁𝔞∈BO : ⋁ 𝔞 ∈ₚ BasicOpens)
                → isLimCone _ _ (F-cone 𝓞ᴮ
                                (condCone.B⋁Cone (λ i → 𝔞 i , 𝔞∈BO i) ⋁𝔞∈BO))
  curriedHelper 𝔞 = PT.elimFin (λ _ → isPropΠ (λ _ → isPropIsLimCone _ _ _))
                     λ x → PT.elim (λ _ → isPropIsLimCone _ _ _) (Σhelper x)
    where
    Σhelper : (x : ∀ i → Σ[ f ∈ R ] D f ≡ 𝔞 i)
              (y : Σ[ g ∈ R ] D g ≡ ⋁ 𝔞)
            → isLimCone _ _ (F-cone 𝓞ᴮ
                            (condCone.B⋁Cone (λ i → 𝔞 i , ∣ x i ∣₁) ∣ y ∣₁))
    Σhelper x y = toSheaf.toLimCone theSheafCone doubleLocAlgCone
                                    algPaths isLimConeDoubleLocAlgCone
      where
      f = fst ∘ x
      h = fst y
      Df≡𝔞 = snd ∘ x
      Dh≡⋁𝔞 = snd y

      open condCone (λ i → 𝔞 i , ∣ f i , Df≡𝔞 i ∣₁)
      theSheafCone = B⋁Cone ∣ h , Dh≡⋁𝔞 ∣₁

      DHelper : D h ≡ [ n , f ] --⋁ (D ∘ f)
      DHelper = Dh≡⋁𝔞 ∙ ⋁Ext (λ i → sym (Df≡𝔞 i)) ∙ ⋁D≡ f

      open Exponentiation R'
      open RadicalIdeal R'
      open DoubleLoc R' h
      open isMultClosedSubset (powersFormMultClosedSubset h)
      open S⁻¹RUniversalProp R' [ h ⁿ|n≥0] (powersFormMultClosedSubset h)
      open CommIdeal R[1/ h ]AsCommRing using ()
                                        renaming (CommIdeal to CommIdealₕ ; _∈_ to _∈ₕ_)

      instance
       _ = snd R[1/ h ]AsCommRing

      -- crucial facts about radical ideals
      h∈√⟨f⟩ : h ∈ √ ⟨ f ⟩[ R' ]
      h∈√⟨f⟩ = isEquivRel→effectiveIso ∼PropValued ∼EquivRel _ _ .fun DHelper .fst zero

      f∈√⟨h⟩ : ∀ i → f i ∈ √ ⟨ h ⟩ₛ
      f∈√⟨h⟩ i = isEquivRel→effectiveIso ∼PropValued ∼EquivRel _ _ .fun
                   (sym DHelper) .fst i

      ff∈√⟨h⟩ : ∀ i j → f i · f j ∈ √ ⟨ h ⟩ₛ
      ff∈√⟨h⟩ i j = √ ⟨ h ⟩ₛ .snd .·Closed (f i) (f∈√⟨h⟩ j)

      f/1 : FinVec (R[1/ h ]) n
      f/1 i = (f i) /1

      1∈⟨f/1⟩ : 1r ∈ₕ ⟨ f/1 ⟩[ R[1/ h ]AsCommRing ]
      1∈⟨f/1⟩ = fromFact h∈√⟨f⟩
       where
       fromFact : h ∈ √ ⟨ f ⟩[ R' ] → 1r ∈ₕ ⟨ f/1 ⟩[ R[1/ h ]AsCommRing ]
       fromFact = PT.rec isPropPropTrunc (uncurry helper1)
        where
        helper1 : (m : ℕ) → h ^ m ∈ ⟨ f ⟩[ R' ] → 1r ∈ₕ ⟨ f/1 ⟩[ R[1/ h ]AsCommRing ]
        helper1 m = PT.map helper2
         where
         helper2 : Σ[ α ∈ FinVec R n ]
                     h ^ m ≡ linearCombination R' α f
                 → Σ[ β ∈ FinVec R[1/ h ] n ]
                     1r ≡ linearCombination R[1/ h ]AsCommRing β f/1
         helper2 (α , hᵐ≡∑αf) = β , path
          where
          open Units R[1/ h ]AsCommRing
          open Sum (CommRing→Ring R[1/ h ]AsCommRing)
          open IsRingHom (snd /1AsCommRingHom)
          open SumMap _ _ /1AsCommRingHom
          instance
           h⁻ᵐ : (h ^ m) /1 ∈ₚ (R[1/ h ]AsCommRing ˣ)
           h⁻ᵐ = [ 1r , h ^ m , ∣ m , refl ∣₁ ]
               , eq/ _ _ ((1r , containsOne) , solve! R')

          β : FinVec R[1/ h ] n
          β i = ((h ^ m) /1) ⁻¹ · α i /1

          /1Path : (h ^ m) /1 ≡ ∑ (λ i → α i /1 · f i /1)
          /1Path = (h ^ m) /1
                 ≡⟨ cong (_/1) hᵐ≡∑αf ⟩
                   (linearCombination R' α f) /1
                 ≡⟨ ∑Map (λ i → α i · f i) ⟩
                   ∑ (λ i → (α i · f i) /1)
                 ≡⟨ ∑Ext (λ i → pres· (α i) (f i)) ⟩
                   ∑ (λ i → α i /1 · f i /1) ∎

          path : 1r ≡ ∑ (λ i →  β i · f/1 i)
          path = 1r
               ≡⟨ sym (·-linv ((h ^ m) /1)) ⟩
                 ((h ^ m) /1) ⁻¹ · (h ^ m) /1
               ≡⟨ cong (((h ^ m) /1) ⁻¹ ·_) /1Path ⟩
                 ((h ^ m) /1) ⁻¹ · ∑ (λ i → α i /1 · f i /1)
               ≡⟨ ∑Mulrdist (((h ^ m) /1) ⁻¹) (λ i → α i /1 · f i /1) ⟩
                 ∑ (λ i →  ((h ^ m) /1) ⁻¹ · (α i /1 · f i /1))
               ≡⟨ ∑Ext (λ i → ·Assoc (((h ^ m) /1) ⁻¹) (α i /1) (f i /1)) ⟩
                 ∑ (λ i →  β i · f/1 i) ∎


      -- Putting everything together:
      -- First, the diagram and limiting cone we get from our lemma
      -- in Cubical.Algebra.Localisation.Limit with R=R[1/h]
      --      ⟨ f₁/1 , ... , fₙ/1 ⟩ = R[1/h]
      --   ⇒  R[1/h] = lim { R[1/h][1/fᵢ] → R[1/h][1/fᵢfⱼ] ← R[1/h][1/fⱼ] }
      doubleLocDiag = locDiagram R[1/ h ]AsCommRing f/1
      doubleLocCone = locCone R[1/ h ]AsCommRing f/1
      isLimConeDoubleLocCone : isLimCone _ _ doubleLocCone
      isLimConeDoubleLocCone = isLimConeLocCone R[1/ h ]AsCommRing f/1 1∈⟨f/1⟩

      -- this gives a limiting cone in R-algebras via _/1/1 : R → R[1/h][1/fᵢ]
      -- note that the pair case looks more complicated as
      -- R[1/h][(fᵢfⱼ)/1/1] =/= R[1/h][(fᵢ/1 · fⱼ/1)/1]
      -- definitionally
      open Cone
      open IsRingHom

      module D i = DoubleLoc R' h (f i)

      /1/1Cone : Cone doubleLocDiag R'
      coneOut /1/1Cone (sing i) = D./1/1AsCommRingHom i
      fst (coneOut /1/1Cone (pair i j i<j)) r =
          [ [ r , 1r , ∣ 0 , refl ∣₁ ] , 1r , ∣ 0 , refl ∣₁ ]
      pres0 (snd (coneOut /1/1Cone (pair i j i<j))) = refl
      pres1 (snd (coneOut /1/1Cone (pair i j i<j))) = refl
      pres+ (snd (coneOut /1/1Cone (pair i j i<j))) x y =
        cong [_] (≡-× (cong [_] (≡-×
                      (cong₂ _+_ (solve! R') (solve! R'))
                      (Σ≡Prop (λ _ → isPropPropTrunc) (solve! R'))))
                      (Σ≡Prop (λ _ → isPropPropTrunc) (sym (·IdR 1r))))
      pres· (snd (coneOut /1/1Cone (pair i j i<j))) x y =
        cong [_] (≡-× (cong [_] (≡-× refl
                      (Σ≡Prop (λ _ → isPropPropTrunc) (sym (·IdR 1r)))))
                      (Σ≡Prop (λ _ → isPropPropTrunc) (sym (·IdR 1r))))
      pres- (snd (coneOut /1/1Cone (pair i j i<j))) _ = refl
      coneOutCommutes /1/1Cone idAr = idCompCommRingHom _
      coneOutCommutes /1/1Cone singPairL = RingHom≡ (funExt
        (λ x → cong [_] (≡-× (cong [_] (≡-× (cong (x ·_) (transportRefl 1r) ∙ ·IdR x)
        (Σ≡Prop (λ _ → isPropPropTrunc) (cong (1r ·_) (transportRefl 1r) ∙ ·IdR 1r))))
        (Σ≡Prop (λ _ → isPropPropTrunc) (cong (1r ·_) (transportRefl 1r) ∙ ·IdR 1r)))))
      coneOutCommutes /1/1Cone singPairR = RingHom≡ (funExt
        (λ x → cong [_] (≡-× (cong [_] (≡-× (cong (x ·_) (transportRefl 1r) ∙ ·IdR x)
        (Σ≡Prop (λ _ → isPropPropTrunc) (cong (1r ·_) (transportRefl 1r) ∙ ·IdR 1r))))
        (Σ≡Prop (λ _ → isPropPropTrunc) (cong (1r ·_) (transportRefl 1r) ∙ ·IdR 1r)))))

      open LimitFromCommRing R' R[1/ h ]AsCommRing (DLShfDiag n ℓ)
                             doubleLocDiag doubleLocCone /1/1Cone

      -- get the desired cone in algebras:
      isConeMor/1 : isConeMor /1/1Cone doubleLocCone /1AsCommRingHom
      isConeMor/1 = isConeMorSingLemma /1/1Cone doubleLocCone
                      (λ _ → RingHom≡ (funExt (λ _ → refl)))

      doubleLocAlgCone = algCone /1AsCommRingHom isConeMor/1
      isLimConeDoubleLocAlgCone : isLimCone _ _ doubleLocAlgCone
      isLimConeDoubleLocAlgCone = reflectsLimits /1AsCommRingHom isConeMor/1
                                                 isLimConeDoubleLocCone

      -- we only give the paths on objects
      -- R[1/h][1/fᵢ] ≡ [1/fᵢ]
      -- R[1/h][1/fᵢfⱼ] ≡ R[1/fᵢfⱼ]
      algPaths : ∀ v → F-ob algDiag v ≡ F-ob (funcComp universalPShf BDiag) v
      algPaths (sing i) = doubleLocCancel (f∈√⟨h⟩ i)
        where
        open DoubleAlgLoc R' h (f i)
      algPaths (pair i j i<j) = path ∙ doubleLocCancel (ff∈√⟨h⟩ i j)
        where
        open DoubleAlgLoc R' h (f i · f j)
        open CommAlgChar R'

        -- the naive def.
        R[1/h][1/fᵢfⱼ]AsCommRingReg = InvertingElementsBase.R[1/_]AsCommRing
                                        R[1/ h ]AsCommRing ((f i · f j) /1)

        path : toCommAlg ( F-ob doubleLocDiag (pair i j i<j)
                         , coneOut /1/1Cone (pair i j i<j))
             ≡ toCommAlg (R[1/h][1/fᵢfⱼ]AsCommRingReg , /1/1AsCommRingHom (f i · f j))
        path =  cong toCommAlg (ΣPathP (p , q))
          where
          eqInR[1/h] : (f i /1) · (f j /1) ≡ (f i · f j) /1
          eqInR[1/h] = sym (/1AsCommRingHom .snd .pres· (f i) (f j))

          p : F-ob doubleLocDiag (pair i j i<j) ≡ R[1/h][1/fᵢfⱼ]AsCommRingReg
          p i = InvertingElementsBase.R[1/_]AsCommRing R[1/ h ]AsCommRing (eqInR[1/h] i)

          q : PathP (λ i → CommRingHom R' (p i)) (coneOut /1/1Cone (pair i j i<j))
                                                 (/1/1AsCommRingHom (f i · f j))
          q = toPathP (RingHom≡ (funExt (
                λ r → cong [_] (≡-× (cong [_] (≡-× (transportRefl _ ∙ transportRefl r)
                    (Σ≡Prop (λ _ → isPropPropTrunc) (transportRefl 1r))))
                    (Σ≡Prop (λ _ → isPropPropTrunc) (transportRefl 1r))))))


 -- our main result
 isSheaf𝓞 : isDLSheaf _ _ 𝓞
 isSheaf𝓞 = isDLSheafDLRan _ _ isSheaf𝓞ᴮ
