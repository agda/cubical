{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Instances.FPAlgebrasSmall where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FPAlgebra
open import Cubical.Algebra.CommAlgebra.FPAlgebra.Instances
open import Cubical.Algebra.CommAlgebra.Instances.Unit
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.BigOps
open import Cubical.Algebra.ZariskiLattice.Base
open import Cubical.Algebra.ZariskiLattice.UniversalProperty

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.CommAlgebras
open import Cubical.Categories.Instances.DistLattices
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Yoneda

open import Cubical.Relation.Binary.Order.Poset

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ


private
 variable
  ℓ ℓ' ℓ'' : Level


module _ (R : CommRing ℓ) where

  open Iso
  open Category hiding (_∘_) renaming (_⋆_ to _⋆c_)
  open Functor
  open NatTrans
  open DistLatticeStr ⦃...⦄
  open CommRingStr ⦃...⦄
  open IsRingHom
  open CommAlgebraHoms
  open IsLatticeHom
  open ZarLat
  open ZarLatUniversalProp


  -- type living in the same universe as the base ring R
  record SmallFPAlgebra : Type ℓ where
    field
      n : ℕ
      m : ℕ
      relations : FinVec ⟨ Polynomials {R = R} n ⟩ m

  open SmallFPAlgebra
  private
    indFPAlg : SmallFPAlgebra → CommAlgebra R ℓ
    indFPAlg A = FPAlgebra (A .n) (A .relations)

  FPAlgebrasSmallCategory : Category ℓ ℓ
  ob FPAlgebrasSmallCategory = SmallFPAlgebra
  Hom[_,_] FPAlgebrasSmallCategory A B =
    CommAlgebraHom (indFPAlg A) (indFPAlg B)
  id FPAlgebrasSmallCategory = idCommAlgebraHom _
  _⋆c_ FPAlgebrasSmallCategory = compCommAlgebraHom _ _ _
  ⋆IdL FPAlgebrasSmallCategory = compIdCommAlgebraHom
  ⋆IdR FPAlgebrasSmallCategory = idCompCommAlgebraHom
  ⋆Assoc FPAlgebrasSmallCategory = compAssocCommAlgebraHom
  isSetHom FPAlgebrasSmallCategory = isSetAlgebraHom _ _


  -- the name of this module will be justified once we have defined
  -- Zariski sheaves on small f.p. algebras
  module SchemesOfFinitePresentation where

    -- "parsimonious" presheaf categories
    fpAlgFunctor = Functor FPAlgebrasSmallCategory (SET ℓ)
    fpAlgFUNCTOR = FUNCTOR FPAlgebrasSmallCategory (SET ℓ)

    -- yoneda in the notation of Demazure-Gabriel
    -- uses η-equality of Categories
    Sp : Functor (FPAlgebrasSmallCategory ^op) fpAlgFUNCTOR
    Sp = YO {C = (FPAlgebrasSmallCategory ^op)}

    -- the Zariski lattice (classifying compact open subobjects)
    private forget = ForgetfulCommAlgebra→CommRing R

    𝓛 : fpAlgFunctor
    F-ob 𝓛 A = ZL (forget .F-ob (indFPAlg A)) , SQ.squash/
    F-hom 𝓛  φ = inducedZarLatHom (forget .F-hom φ) .fst
    F-id 𝓛 = cong (λ x → inducedZarLatHom x .fst) (forget .F-id)
            ∙ cong fst (inducedZarLatHomId _)
    F-seq 𝓛 _ _ = cong (λ x → inducedZarLatHom x .fst) (forget .F-seq _ _)
                 ∙ cong fst (inducedZarLatHomSeq _ _)

    CompactOpen : fpAlgFunctor → Type ℓ
    CompactOpen X = X ⇒ 𝓛

    isAffine : fpAlgFunctor → Type ℓ
    isAffine X = ∃[ A ∈ SmallFPAlgebra ] (Sp .F-ob A) ≅ᶜ X

    -- the induced subfunctor
    ⟦_⟧ᶜᵒ : {X : fpAlgFunctor} (U : CompactOpen X) → fpAlgFunctor
    F-ob (⟦_⟧ᶜᵒ {X = X} U) A = (Σ[ x ∈ X .F-ob A .fst  ] U .N-ob A x ≡ D _ 1r)
                                  , isSetΣSndProp (X .F-ob A .snd) λ _ → squash/ _ _
     where instance _ = snd (forget .F-ob (indFPAlg A))
    F-hom (⟦_⟧ᶜᵒ {X = X} U) {x = A} {y = B} φ (x , Ux≡D1) = (X .F-hom φ x) , path
      where
      instance
        _ = (forget .F-ob (indFPAlg A)) .snd
        _ = (forget .F-ob (indFPAlg B)) .snd
      open IsLatticeHom
      path : U .N-ob B (X .F-hom φ x) ≡ D _ 1r
      path = U .N-ob B (X .F-hom φ x) ≡⟨ funExt⁻ (U .N-hom φ) x ⟩
             𝓛 .F-hom φ (U .N-ob A x) ≡⟨ cong (𝓛 .F-hom φ) Ux≡D1 ⟩
             𝓛 .F-hom φ (D _ 1r)      ≡⟨ inducedZarLatHom (forget .F-hom φ) .snd .pres1 ⟩
             D _ 1r ∎
    F-id (⟦_⟧ᶜᵒ {X = X} U) = funExt (λ x → Σ≡Prop (λ _ → squash/ _ _)
                                       (funExt⁻ (X .F-id) (x .fst)))
    F-seq (⟦_⟧ᶜᵒ {X = X} U) φ ψ = funExt (λ x → Σ≡Prop (λ _ → squash/ _ _)
                                            (funExt⁻ (X .F-seq φ ψ) (x .fst)))

    isAffineCompactOpen : {X : fpAlgFunctor} (U : CompactOpen X) → Type ℓ
    isAffineCompactOpen U = isAffine ⟦ U ⟧ᶜᵒ

    -- the dist. lattice of compact opens
    CompOpenDistLattice : Functor fpAlgFUNCTOR (DistLatticesCategory {ℓ} ^op)
    fst (F-ob CompOpenDistLattice X) = CompactOpen X

    -- lattice structure induce by internal lattice object 𝓛
    N-ob (DistLatticeStr.0l (snd (F-ob CompOpenDistLattice X))) A _ = 0l
      where instance _ = ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
    N-hom (DistLatticeStr.0l (snd (F-ob CompOpenDistLattice X))) _ = funExt λ _ → refl

    N-ob (DistLatticeStr.1l (snd (F-ob CompOpenDistLattice X))) A _ = 1l
      where instance _ = ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
    N-hom (DistLatticeStr.1l (snd (F-ob CompOpenDistLattice X))) {x = A} {y = B} φ = funExt λ _ → path
      where
      instance
        _ = (forget .F-ob (indFPAlg A)) .snd
        _ = (forget .F-ob (indFPAlg B)) .snd
        _ = ZariskiLattice (forget .F-ob (indFPAlg B)) .snd
      path : D _ 1r ≡ D _ (φ .fst 1r) ∨l 0l
      path = cong (D (forget .F-ob (indFPAlg B))) (sym (forget .F-hom φ .snd .pres1))
           ∙ sym (∨lRid _)

    N-ob ((snd (F-ob CompOpenDistLattice X) DistLatticeStr.∨l U) V) A x =
      U .N-ob A x ∨l V .N-ob A x
      where instance _ = ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
    N-hom ((snd (F-ob CompOpenDistLattice X) DistLatticeStr.∨l U) V)  {x = A} {y = B} φ =
      funExt path
      where
      instance
        _ = ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
        _ = ZariskiLattice (forget .F-ob (indFPAlg B)) .snd
      path : ∀ x → U .N-ob B (X .F-hom φ x) ∨l V .N-ob B (X .F-hom φ x)
                 ≡ 𝓛 .F-hom φ (U .N-ob A x ∨l V .N-ob A x)
      path x = U .N-ob B (X .F-hom φ x) ∨l V .N-ob B (X .F-hom φ x)
             ≡⟨ cong₂ _∨l_ (funExt⁻ (U .N-hom φ) x) (funExt⁻ (V .N-hom φ) x) ⟩
               𝓛 .F-hom φ (U .N-ob A x) ∨l 𝓛 .F-hom φ (V .N-ob A x)
             ≡⟨ sym (inducedZarLatHom (forget .F-hom φ) .snd .pres∨l _ _) ⟩
               𝓛 .F-hom φ (U .N-ob A x ∨l V .N-ob A x) ∎

    N-ob ((snd (F-ob CompOpenDistLattice X) DistLatticeStr.∧l U) V) A x =
      U .N-ob A x ∧l V .N-ob A x
      where instance _ = ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
    N-hom ((snd (F-ob CompOpenDistLattice X) DistLatticeStr.∧l U) V) {x = A} {y = B} φ =
      funExt path
      where
      instance
        _ = ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
        _ = ZariskiLattice (forget .F-ob (indFPAlg B)) .snd
      path : ∀ x → U .N-ob B (X .F-hom φ x) ∧l V .N-ob B (X .F-hom φ x)
                 ≡ 𝓛 .F-hom φ (U .N-ob A x ∧l V .N-ob A x)
      path x = U .N-ob B (X .F-hom φ x) ∧l V .N-ob B (X .F-hom φ x)
             ≡⟨ cong₂ _∧l_ (funExt⁻ (U .N-hom φ) x) (funExt⁻ (V .N-hom φ) x) ⟩
               𝓛 .F-hom φ (U .N-ob A x) ∧l 𝓛 .F-hom φ (V .N-ob A x)
             ≡⟨ sym (inducedZarLatHom (forget .F-hom φ) .snd .pres∧l _ _) ⟩
               𝓛 .F-hom φ (U .N-ob A x ∧l V .N-ob A x) ∎

    DistLatticeStr.isDistLattice (snd (F-ob CompOpenDistLattice X)) =
      makeIsDistLattice∧lOver∨l
        isSetNatTrans
        (λ _ _ _ → makeNatTransPath (funExt₂
                     (λ A _ → ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
                                .DistLatticeStr.∨lAssoc _ _ _)))
        (λ _ →     makeNatTransPath (funExt₂
                     (λ A _ → ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
                                .DistLatticeStr.∨lRid _)))
        (λ _ _ →   makeNatTransPath (funExt₂
                     (λ A _ → ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
                                .DistLatticeStr.∨lComm _ _)))
        (λ _ _ _ → makeNatTransPath (funExt₂
                     (λ A _ → ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
                                .DistLatticeStr.∧lAssoc _ _ _)))
        (λ _ →     makeNatTransPath (funExt₂
                     (λ A _ → ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
                                .DistLatticeStr.∧lRid _)))
        (λ _ _ →   makeNatTransPath (funExt₂
                     (λ A _ → ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
                               .DistLatticeStr.∧lComm _ _)))
        (λ _ _ →   makeNatTransPath (funExt₂ -- don't know why ∧lAbsorb∨l doesn't work
                     (λ A _ → ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
                                .DistLatticeStr.absorb _ _ .snd)))
        (λ _ _ _ → makeNatTransPath (funExt₂ -- same here
                     (λ A _ → ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
                                .DistLatticeStr.∧l-dist-∨l _ _ _ .fst)))

    -- (contravariant) action on morphisms
    fst (F-hom CompOpenDistLattice α) = α ●ᵛ_
    pres0 (snd (F-hom CompOpenDistLattice α)) = makeNatTransPath (funExt₂ λ _ _ → refl)
    pres1 (snd (F-hom CompOpenDistLattice α)) = makeNatTransPath (funExt₂ λ _ _ → refl)
    pres∨l (snd (F-hom CompOpenDistLattice α)) _ _ = makeNatTransPath (funExt₂ λ _ _ → refl)
    pres∧l (snd (F-hom CompOpenDistLattice α)) _ _ = makeNatTransPath (funExt₂ λ _ _ → refl)

    -- functoriality
    F-id CompOpenDistLattice = LatticeHom≡f _ _
                                 (funExt λ _ → makeNatTransPath (funExt₂ λ _ _ → refl))
    F-seq CompOpenDistLattice _ _ = LatticeHom≡f _ _
                                      (funExt λ _ → makeNatTransPath (funExt₂ λ _ _ → refl))

    -- the above is actually a functor into dist. lattices over 𝓛 R
    open import Cubical.Categories.Constructions.Slice
                    (DistLatticesCategory {ℓ} ^op) (ZariskiLattice R)
         renaming (SliceCat to DistLatticeᵒᵖ/𝓛R)
    open SliceOb
    open SliceHom
    open IsZarMap
    private
      d : (X : fpAlgFunctor) → fst R → CompactOpen X
      N-ob (d X r) A _ = D _ (r ⋆ 1a)
        where open CommAlgebraStr (indFPAlg A .snd)
      N-hom (d X r) {A} {B} φ = funExt (λ _ → sym path)
        where
        open IsAlgebraHom
        open CommAlgebraStr ⦃...⦄ using (_⋆_ ; 1a)
        instance
          _ = indFPAlg A .snd
          _ = indFPAlg B .snd
          _ = ZariskiLattice (forget .F-ob (indFPAlg B)) .snd
        path : D _ (φ .fst (r ⋆ 1a)) ∨l 0l ≡ D _ (r ⋆ 1a)
        path = D _ (φ .fst (r ⋆ 1a)) ∨l 0l ≡⟨ ∨lRid _ ⟩
               D _ (φ .fst (r ⋆ 1a))       ≡⟨ cong (D _) (φ .snd .pres⋆ _ _) ⟩
               D _ (r ⋆ φ .fst 1a)         ≡⟨ cong (λ x → D _ (r ⋆ x)) (φ .snd .pres1) ⟩
               D _ (r ⋆ 1a) ∎

      dIsZarMap : ∀ (X : fpAlgFunctor) → IsZarMap R (F-ob CompOpenDistLattice X) (d X)
      pres0 (dIsZarMap X) = makeNatTransPath (funExt₂ (λ A _ →
        let open AlgebraTheory (CommRing→Ring R) (CommAlgebra→Algebra (indFPAlg A))
        in cong (D _) (⋆AnnihilL _) ∙ isZarMapD _ .pres0))
      pres1 (dIsZarMap X) = makeNatTransPath (funExt₂ (λ A _ →
        cong (D _) (CommAlgebraStr.⋆IdL (indFPAlg A .snd) _) ∙ isZarMapD _ .pres1))
      ·≡∧ (dIsZarMap X) r s = makeNatTransPath (funExt₂ (λ A _ →
        let open AlgebraTheory (CommRing→Ring R) (CommAlgebra→Algebra (indFPAlg A))
            open CommAlgebraStr ⦃...⦄ using (_⋆_ ; 1a) renaming (_·_ to _·a_ ; ·IdL to ·aIdL)
            instance _ = indFPAlg A .snd
                     _ = R .snd
                     _ = ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
        in D _((r · s) ⋆ 1a) ≡⟨ cong (λ x → D _ ((r · s) ⋆ x)) (sym (·aIdL 1a)) ⟩
           D _((r · s) ⋆ (1a ·a 1a)) ≡⟨ cong (D _) (⋆Dist· _ _ _ _) ⟩
           D _((r ⋆ 1a) ·a (s ⋆ 1a)) ≡⟨ isZarMapD _ .·≡∧ _ _ ⟩
           D _(r ⋆ 1a) ∧l D _ (s ⋆ 1a) ∎))
      +≤∨ (dIsZarMap X) r s = makeNatTransPath (funExt₂ (λ A _ →
        let open CommAlgebraStr ⦃...⦄ using (_⋆_ ; 1a ; ⋆DistL+)
            open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice
                                 (ZariskiLattice (forget .F-ob (indFPAlg A)))))
            instance _ = indFPAlg A .snd
                     _ = ZariskiLattice (forget .F-ob (indFPAlg A)) .snd
        in subst (_≤ D _(r ⋆ 1a) ∨l D _ (s ⋆ 1a)) (cong (D _) (sym (⋆DistL+ _ _ _)))
                 (isZarMapD _ .+≤∨ _ _)))


      uniqueHom𝓛R→CompOpen : (X : fpAlgFunctor)
                            → ∃![ χ ∈ DistLatticeHom (ZariskiLattice R)
                                                     (F-ob CompOpenDistLattice X) ]
                                  χ .fst ∘ D R ≡ d X
      uniqueHom𝓛R→CompOpen X = ZLHasUniversalProp R (F-ob CompOpenDistLattice X)
                                                     (d X) (dIsZarMap X)

    CompOpenDistLatticeOver : Functor fpAlgFUNCTOR DistLatticeᵒᵖ/𝓛R
    S-ob (F-ob CompOpenDistLatticeOver X) = CompOpenDistLattice .F-ob X

    -- the induced morphism 𝓛 R → CompactOpen X
    S-arr (F-ob CompOpenDistLatticeOver X) = uniqueHom𝓛R→CompOpen X .fst .fst
    S-hom (F-hom CompOpenDistLatticeOver α) = CompOpenDistLattice .F-hom α
    S-comm (F-hom CompOpenDistLatticeOver {X} {Y} α) =
      sym (cong fst (uniqueHom𝓛R→CompOpen X .snd (χ' , χ'Path)))
      where
      χ' = CompOpenDistLattice .F-hom α ∘dl uniqueHom𝓛R→CompOpen Y .fst .fst
      χ'Path : χ' .fst ∘ D R ≡ d X
      χ'Path = cong (CompOpenDistLattice .F-hom α .fst ∘_)
                    (uniqueHom𝓛R→CompOpen Y .fst .snd)
             ∙ funExt (λ r → makeNatTransPath (funExt₂ (λ _ _ → refl)))
    F-id CompOpenDistLatticeOver = SliceHom-≡-intro' (CompOpenDistLattice .F-id)
    F-seq CompOpenDistLatticeOver _ _ = SliceHom-≡-intro' (CompOpenDistLattice .F-seq _ _)


    module _ (X : fpAlgFunctor) where
      open Join (CompOpenDistLattice .F-ob X)
      private instance _ = (CompOpenDistLattice .F-ob X) .snd

      record AffineCover : Type ℓ where
        field
          n : ℕ
          U : FinVec (CompactOpen X) n
          covers : ⋁ U ≡ 1l -- TODO: equivalent to X ≡ ⟦ ⋁ U ⟧ᶜᵒ
          isAffineU : ∀ i → isAffineCompactOpen (U i)

      hasAffineCover : Type ℓ
      hasAffineCover = ∥ AffineCover ∥₁
      -- TODO: A fp-alg-functor is a scheme of finite presentation (over R)
      -- if it is a Zariski sheaf and has an affine cover
