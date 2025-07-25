{-

   The definition of compact open subfunctors of a ℤ-functor X:

     U ↪ Sp(A) is compact open if it is given by a f.g. ideal of A,
     i.e. if ∃ f₁, ... ,fₙ : A s.t. for all rings B:
                U(B) = { φ : Hom(A,B) | ⟨ φf₁ , ... , φfₙ ⟩ = B }

     U ↪ X is compact open, if pulling back along any A-valued point
     Sp(A) → X gives a compact open of Sp(A).

     By observing that compact open subfunctors of affine schemes
     are in 1-1 correspondence with radicals of f.g. ideals,
     we get that compact open subfunctors are classified by the
     ℤ-functor that sends a ring to its Zariski lattice.

-}


{-# OPTIONS --lossy-unification #-}
module Cubical.AlgebraicGeometry.Functorial.ZFunctors.CompactOpen where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels


open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Data.FinData

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.BigOps

open import Cubical.AlgebraicGeometry.ZariskiLattice.Base
open import Cubical.AlgebraicGeometry.ZariskiLattice.UniversalProperty
open import Cubical.AlgebraicGeometry.ZariskiLattice.Properties
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.Base

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.DistLattices
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Site.Sheaf
open import Cubical.Categories.Site.Instances.ZariskiCommRing
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Yoneda

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ

open import Cubical.Relation.Binary.Order.Poset


module _ {ℓ : Level} where

  open Iso
  open Functor
  open NatTrans
  open NatIso
  open DistLatticeStr ⦃...⦄
  open CommRingStr ⦃...⦄
  open IsCommRingHom
  open IsLatticeHom
  open ZarLat
  open ZarLatUniversalProp

  -- the Zariski lattice functor classifying compact open subobjects
  ZarLatFun : ℤFunctor {ℓ = ℓ}
  F-ob ZarLatFun A = ZL A , SQ.squash/
  F-hom ZarLatFun φ = inducedZarLatHom φ .fst
  F-id ZarLatFun {A} = cong fst (inducedZarLatHomId A)
  F-seq ZarLatFun φ ψ = cong fst (inducedZarLatHomSeq φ ψ)

  -- this is a separated presheaf
  -- (TODO: prove this a sheaf)
  isSeparatedZarLatFun : isSeparated zariskiCoverage ZarLatFun
  isSeparatedZarLatFun A (unimodvec n f 1∈⟨f₁,⋯,fₙ⟩) u w uRest≡wRest =
    u                         ≡⟨ sym (∧lLid _) ⟩
    1l ∧l u                  ≡⟨ congL _∧l_ D1≡⋁Dfᵢ ⟩
    (⋁ (D A ∘ f)) ∧l u       ≡⟨ ⋁Meetldist _ _ ⟩
    ⋁ (λ i → D A (f i) ∧l u) ≡⟨ ⋁Ext Dfᵢ∧u≡Dfᵢ∧w ⟩
    ⋁ (λ i → D A (f i) ∧l w) ≡⟨ sym (⋁Meetldist _ _) ⟩
    (⋁ (D A ∘ f)) ∧l w       ≡⟨ congL _∧l_ (sym D1≡⋁Dfᵢ) ⟩
    1l ∧l w                  ≡⟨ ∧lLid _ ⟩
    w ∎
    where
    open Join (ZariskiLattice A)
    open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice (ZariskiLattice A)))
         using (IndPoset)
    open LatticeTheory (DistLattice→Lattice (ZariskiLattice A))
    open PosetStr (IndPoset .snd)
    open IsSupport (isSupportD A)
    open RadicalIdeal A
    instance
      _ = A .snd
      _ = ZariskiLattice A .snd

    D1≡⋁Dfᵢ : 1l ≡ ⋁ (D A ∘ f)
    D1≡⋁Dfᵢ = is-antisym _ _
                (supportRadicalIneq f 1r (∈→∈√ _ _ 1∈⟨f₁,⋯,fₙ⟩))
                  (1lRightAnnihilates∨l _)

    Dfᵢ∧u≡Dfᵢ∧w : ∀ i → D A (f i) ∧l u ≡ D A (f i) ∧l w
    Dfᵢ∧u≡Dfᵢ∧w i =
        D A (f i) ∧l u
      ≡⟨ sym (cong fst (funExt⁻ (cong fst toLocToDown≡ToDown) u)) ⟩
        locToDownHom .fst (inducedZarLatHom /1AsCommRingHom .fst u) .fst
      ≡⟨ cong (λ x → locToDownHom .fst x .fst) (uRest≡wRest i) ⟩
        locToDownHom .fst (inducedZarLatHom /1AsCommRingHom .fst w) .fst
      ≡⟨ cong fst (funExt⁻ (cong fst toLocToDown≡ToDown) w) ⟩
        D A (f i) ∧l w ∎
      where
      open InvertingElementsBase.UniversalProp A (f i)
      open LocDownSetIso A (f i)

  CompactOpen : ℤFunctor → Type (ℓ-suc ℓ)
  CompactOpen X = X ⇒ ZarLatFun

  -- the induced subfunctor
  ⟦_⟧ᶜᵒ : {X : ℤFunctor} (U : CompactOpen X) → ℤFunctor
  F-ob (⟦_⟧ᶜᵒ {X = X} U) A = (Σ[ x ∈ X .F-ob A .fst  ] U .N-ob A x ≡ D A 1r)
                                , isSetΣSndProp (X .F-ob A .snd) λ _ → squash/ _ _
   where instance _ = snd A
  F-hom (⟦_⟧ᶜᵒ {X = X} U) {x = A} {y = B} φ (x , Ux≡D1) = (X .F-hom φ x) , path
    where
    instance
      _ = A .snd
      _ = B .snd
    open IsLatticeHom
    path : U .N-ob B (X .F-hom φ x) ≡ D B 1r
    path = U .N-ob B (X .F-hom φ x)         ≡⟨ funExt⁻ (U .N-hom φ) x ⟩
           ZarLatFun .F-hom φ (U .N-ob A x) ≡⟨ cong (ZarLatFun .F-hom φ) Ux≡D1 ⟩
           ZarLatFun .F-hom φ (D A 1r)      ≡⟨ inducedZarLatHom φ .snd .pres1 ⟩
           D B 1r ∎
  F-id (⟦_⟧ᶜᵒ {X = X} U) = funExt (λ x → Σ≡Prop (λ _ → squash/ _ _)
                                     (funExt⁻ (X .F-id) (x .fst)))
  F-seq (⟦_⟧ᶜᵒ {X = X} U) φ ψ = funExt (λ x → Σ≡Prop (λ _ → squash/ _ _)
                                          (funExt⁻ (X .F-seq φ ψ) (x .fst)))


  isAffineCompactOpen : {X : ℤFunctor} (U : CompactOpen X) → Type (ℓ-suc ℓ)
  isAffineCompactOpen U = isAffine ⟦ U ⟧ᶜᵒ


  -- the (big) dist. lattice of compact opens
  CompOpenDistLattice : Functor ℤFUNCTOR (DistLatticesCategory {ℓ = ℓ-suc ℓ} ^op)
  fst (F-ob CompOpenDistLattice X) = CompactOpen X

  -- lattice structure induce by internal lattice object ZarLatFun
  N-ob (DistLatticeStr.0l (snd (F-ob CompOpenDistLattice X))) A _ = 0l
    where instance _ = ZariskiLattice A .snd
  N-hom (DistLatticeStr.0l (snd (F-ob CompOpenDistLattice X))) _ = funExt λ _ → refl

  N-ob (DistLatticeStr.1l (snd (F-ob CompOpenDistLattice X))) A _ = 1l
    where instance _ = ZariskiLattice A .snd
  N-hom (DistLatticeStr.1l (snd (F-ob CompOpenDistLattice X))) {x = A} {y = B} φ = funExt λ _ → path
    where
    instance
      _ = A .snd
      _ = B .snd
      _ = ZariskiLattice B .snd
    path : D B 1r ≡ D B (φ .fst 1r) ∨l 0l
    path = cong (D B) (sym (φ .snd .pres1)) ∙ sym (∨lRid _)

  N-ob ((snd (F-ob CompOpenDistLattice X) DistLatticeStr.∨l U) V) A x = U .N-ob A x ∨l V .N-ob A x
    where instance _ = ZariskiLattice A .snd
  N-hom ((snd (F-ob CompOpenDistLattice X) DistLatticeStr.∨l U) V)  {x = A} {y = B} φ = funExt path
    where
    instance
      _ = ZariskiLattice A .snd
      _ = ZariskiLattice B .snd
    path : ∀ x → U .N-ob B (X .F-hom φ x) ∨l V .N-ob B (X .F-hom φ x)
               ≡ ZarLatFun .F-hom φ (U .N-ob A x ∨l V .N-ob A x)
    path x = U .N-ob B (X .F-hom φ x) ∨l V .N-ob B (X .F-hom φ x)
           ≡⟨ cong₂ _∨l_ (funExt⁻ (U .N-hom φ) x) (funExt⁻ (V .N-hom φ) x) ⟩
             ZarLatFun .F-hom φ (U .N-ob A x) ∨l ZarLatFun .F-hom φ (V .N-ob A x)
           ≡⟨ sym (inducedZarLatHom φ .snd .pres∨l _ _) ⟩
             ZarLatFun .F-hom φ (U .N-ob A x ∨l V .N-ob A x) ∎

  N-ob ((snd (F-ob CompOpenDistLattice X) DistLatticeStr.∧l U) V) A x = U .N-ob A x ∧l V .N-ob A x
    where instance _ = ZariskiLattice A .snd
  N-hom ((snd (F-ob CompOpenDistLattice X) DistLatticeStr.∧l U) V)  {x = A} {y = B} φ = funExt path
    where
    instance
      _ = ZariskiLattice A .snd
      _ = ZariskiLattice B .snd
    path : ∀ x → U .N-ob B (X .F-hom φ x) ∧l V .N-ob B (X .F-hom φ x)
               ≡ ZarLatFun .F-hom φ (U .N-ob A x ∧l V .N-ob A x)
    path x = U .N-ob B (X .F-hom φ x) ∧l V .N-ob B (X .F-hom φ x)
           ≡⟨ cong₂ _∧l_ (funExt⁻ (U .N-hom φ) x) (funExt⁻ (V .N-hom φ) x) ⟩
             ZarLatFun .F-hom φ (U .N-ob A x) ∧l ZarLatFun .F-hom φ (V .N-ob A x)
           ≡⟨ sym (inducedZarLatHom φ .snd .pres∧l _ _) ⟩
             ZarLatFun .F-hom φ (U .N-ob A x ∧l V .N-ob A x) ∎

  DistLatticeStr.isDistLattice (snd (F-ob CompOpenDistLattice X)) = makeIsDistLattice∧lOver∨l
    isSetNatTrans
    (λ _ _ _ → makeNatTransPath (funExt₂
                 (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∨lAssoc _ _ _)))
    (λ _ → makeNatTransPath (funExt₂ (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∨lRid _)))
    (λ _ _ → makeNatTransPath (funExt₂ (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∨lComm _ _)))
    (λ _ _ _ → makeNatTransPath (funExt₂
                 (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∧lAssoc _ _ _)))
    (λ _ → makeNatTransPath (funExt₂ (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∧lRid _)))
    (λ _ _ → makeNatTransPath (funExt₂ (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∧lComm _ _)))
    (λ _ _ → makeNatTransPath (funExt₂ -- don't know why ∧lAbsorb∨l doesn't work
               (λ A _ → ZariskiLattice A .snd .DistLatticeStr.absorb _ _ .snd)))
    (λ _ _ _ → makeNatTransPath (funExt₂ -- same here
                 (λ A _ → ZariskiLattice A .snd .DistLatticeStr.∧l-dist-∨l _ _ _ .fst)))

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


  -- useful lemmas
  module _ (X : ℤFunctor) where
    open isIsoC
    private instance _ = (CompOpenDistLattice .F-ob X) .snd

    compOpenTopNatIso : NatIso X ⟦ 1l ⟧ᶜᵒ
    N-ob (trans compOpenTopNatIso) _ φ = φ , refl
    N-hom (trans compOpenTopNatIso) _ = funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) refl
    inv (nIso compOpenTopNatIso B) = fst
    sec (nIso compOpenTopNatIso B) = funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) refl
    ret (nIso compOpenTopNatIso B) = funExt λ _ → refl


  module _ (X : ℤFunctor) where
    open isIsoC
    open Join (CompOpenDistLattice .F-ob X)
    open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice (CompOpenDistLattice .F-ob X)))
    open PosetStr (IndPoset .snd) hiding (_≤_)
    open LatticeTheory ⦃...⦄
    private instance _ = (CompOpenDistLattice .F-ob X) .snd

    compOpenGlobalIncl : (U : CompactOpen X) → ⟦ U ⟧ᶜᵒ ⇒ X
    N-ob (compOpenGlobalIncl U) A = fst
    N-hom (compOpenGlobalIncl U) φ = refl

    compOpenIncl : {U V : CompactOpen X} → V ≤ U → ⟦ V ⟧ᶜᵒ ⇒ ⟦ U ⟧ᶜᵒ
    N-ob (compOpenIncl {U = U} {V = V} V≤U) A (x , Vx≡D1) = x , path
      where
      instance
        _ = A .snd
        _ = ZariskiLattice A .snd
        _ = DistLattice→Lattice (ZariskiLattice A)
      path : U .N-ob A x ≡ D A 1r
      path = U .N-ob A x                ≡⟨ funExt⁻ (funExt⁻ (cong N-ob (sym V≤U)) A) x ⟩
             V .N-ob A x ∨l U .N-ob A x ≡⟨ cong (_∨l U .N-ob A x) Vx≡D1 ⟩
             D A 1r ∨l U .N-ob A x      ≡⟨ 1lLeftAnnihilates∨l _ ⟩
             D A 1r ∎
    N-hom (compOpenIncl V≤U) φ = funExt λ x → Σ≡Prop (λ _ → squash/ _ _) refl

    -- this is essentially U∧_
    compOpenDownHom : (U : CompactOpen X)
                    → DistLatticeHom (CompOpenDistLattice .F-ob X)
                                     (CompOpenDistLattice .F-ob ⟦ U ⟧ᶜᵒ)
    compOpenDownHom U = CompOpenDistLattice .F-hom (compOpenGlobalIncl U)

    module _ {U V : CompactOpen X} (V≤U : V ≤ U) where
      -- We need this separate definition to avoid termination checker issues,
      -- but we don't understand why.
      private
        compOpenDownHomFun : (A : CommRing ℓ)
                           → ⟦ V ⟧ᶜᵒ .F-ob A .fst
                           → ⟦ compOpenDownHom U .fst V ⟧ᶜᵒ .F-ob A .fst
        compOpenDownHomFun A v = (compOpenIncl V≤U ⟦ A ⟧) v , snd v

      compOpenDownHomNatIso : NatIso ⟦ V ⟧ᶜᵒ ⟦ compOpenDownHom U .fst V ⟧ᶜᵒ
      N-ob (trans compOpenDownHomNatIso) = compOpenDownHomFun
      N-hom (trans compOpenDownHomNatIso) _ =
        funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) (Σ≡Prop (λ _ → squash/ _ _) refl)
      inv (nIso compOpenDownHomNatIso A) ((x , Ux≡D1) , Vx≡D1) = x , Vx≡D1
      sec (nIso compOpenDownHomNatIso A) =
        funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) (Σ≡Prop (λ _ → squash/ _ _) refl)
      ret (nIso compOpenDownHomNatIso A) = funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) refl

    compOpenInclId : ∀ {U : CompactOpen X} → compOpenIncl (is-refl U) ≡ idTrans ⟦ U ⟧ᶜᵒ
    compOpenInclId = makeNatTransPath (funExt₂ (λ _ _ → Σ≡Prop (λ _ → squash/ _ _) refl))

    compOpenInclSeq : ∀ {U V W : CompactOpen X} (U≤V : U ≤ V) (V≤W : V ≤ W)
                    → compOpenIncl (is-trans _ _ _ U≤V V≤W)
                    ≡ compOpenIncl U≤V ●ᵛ compOpenIncl V≤W
    compOpenInclSeq _ _ = makeNatTransPath
                            (funExt₂ (λ _ _ → Σ≡Prop (λ _ → squash/ _ _) refl))


    -- the structure sheaf
    private COᵒᵖ = (DistLatticeCategory (CompOpenDistLattice .F-ob X)) ^op

    strDLSh : Functor COᵒᵖ (CommRingsCategory {ℓ = ℓ-suc ℓ})
    F-ob strDLSh  U = 𝓞 .F-ob ⟦ U ⟧ᶜᵒ
    F-hom strDLSh U≥V = 𝓞 .F-hom (compOpenIncl U≥V)
    F-id strDLSh = cong (𝓞 .F-hom) compOpenInclId ∙ 𝓞 .F-id
    F-seq strDLSh _ _ = cong (𝓞 .F-hom) (compOpenInclSeq _ _) ∙ 𝓞 .F-seq _ _


  -- important lemma
  -- Compact opens of Zariski sheaves are sheaves
  presLocalCompactOpen : (X : ℤFunctor) (U : CompactOpen X) → isLocal X → isLocal ⟦ U ⟧ᶜᵒ
  presLocalCompactOpen X U isLocalX R um@(unimodvec _ f _) = isoToIsEquiv isoU
    where
    open Coverage zariskiCoverage
    open InvertingElementsBase R
    instance _ = R .snd

    fᵢCoverR = covers R .snd um

    isoX : Iso (X .F-ob R .fst) (CompatibleFamily X fᵢCoverR)
    isoX = equivToIso (elementToCompatibleFamily _ _ , isLocalX R um)

    compatibleFamIncl : (CompatibleFamily ⟦ U ⟧ᶜᵒ fᵢCoverR) → (CompatibleFamily X fᵢCoverR)
    compatibleFamIncl fam = (fst ∘ fst fam)
                          , λ i j B φ ψ φψComm → cong fst (fam .snd i j B φ ψ φψComm)

    compatibleFamIncl≡ : ∀ (y : Σ[ x ∈ X .F-ob R .fst  ] U .N-ob R x ≡ D R 1r)
                       → compatibleFamIncl (elementToCompatibleFamily ⟦ U ⟧ᶜᵒ fᵢCoverR y)
                       ≡ elementToCompatibleFamily X fᵢCoverR (y .fst)
    compatibleFamIncl≡ y = CompatibleFamily≡ _ _ _ _ λ _ → refl

    isoU : Iso (Σ[ x ∈ X .F-ob R .fst  ] U .N-ob R x ≡ D R 1r)
               (CompatibleFamily ⟦ U ⟧ᶜᵒ fᵢCoverR)
    fun isoU = elementToCompatibleFamily _ _
    fst (inv isoU fam) = isoX .inv (compatibleFamIncl fam)
    snd (inv isoU fam) = -- U (x) ≡ D(1)
                         -- knowing that U(x/1)¸≡ D(1) in R[1/fᵢ]
      let x = isoX .inv (compatibleFamIncl fam) in
      isSeparatedZarLatFun R um (U .N-ob R x) (D R 1r)
        λ i → let open UniversalProp (f i)
                  instance _ = R[1/ (f i) ]AsCommRing .snd in

                inducedZarLatHom /1AsCommRingHom .fst (U .N-ob R x)

              ≡⟨ funExt⁻ (sym (U .N-hom /1AsCommRingHom)) x ⟩

                U .N-ob R[1/ (f i) ]AsCommRing (X .F-hom /1AsCommRingHom x)

              ≡⟨ cong (U .N-ob R[1/ f i ]AsCommRing)
                      (funExt⁻ (cong fst (isoX .rightInv (compatibleFamIncl fam))) i) ⟩

                U .N-ob R[1/ (f i) ]AsCommRing (fam .fst i .fst)

              ≡⟨ fam .fst i .snd ⟩

                D R[1/ (f i) ]AsCommRing 1r

              ≡⟨ sym (inducedZarLatHom /1AsCommRingHom .snd .pres1) ⟩

                inducedZarLatHom /1AsCommRingHom .fst (D R 1r) ∎

    rightInv isoU fam =
      Σ≡Prop (λ _ → isPropIsCompatibleFamily _ _ _)
        (funExt λ i → Σ≡Prop (λ _ → squash/ _ _)
                        (funExt⁻ (cong fst
                          (isoX .rightInv (compatibleFamIncl fam))) i))
    leftInv isoU y = Σ≡Prop (λ _ → squash/ _ _)
                            (cong (isoX .inv) (compatibleFamIncl≡ y)
                              ∙ isoX .leftInv (y .fst))
