{-

  Compact open subfunctors of affine schemes are qcqs-schemes
  The proof proceeds by
    1. Defining standard/basic compact opens of affines and proving that they are affine
    2. Proving that arbitrary compact opens of affines are qcqs-schemes

  TODO: prove that compact opens of qcqs-schemes are qcqs-schemes

-}

{-# OPTIONS --lossy-unification #-}
module Cubical.AlgebraicGeometry.Functorial.ZFunctors.OpenSubscheme where

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

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.BigOps

open import Cubical.AlgebraicGeometry.ZariskiLattice.Base
open import Cubical.AlgebraicGeometry.ZariskiLattice.UniversalProperty
open import Cubical.AlgebraicGeometry.ZariskiLattice.Properties
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.Base
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.CompactOpen
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.QcQsScheme

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor

open import Cubical.Categories.Site.Instances.ZariskiCommRing
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Yoneda


open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ

open import Cubical.Relation.Binary.Order.Poset


-- standard affine opens
module StandardOpens {ℓ : Level} (R : CommRing ℓ) (f : R .fst) where

  open Iso
  open Functor
  open NatTrans
  open NatIso
  open isIsoC
  open DistLatticeStr ⦃...⦄
  open CommRingStr ⦃...⦄
  open IsCommRingHom
  open IsLatticeHom
  open ZarLat

  open InvertingElementsBase R
  open UniversalProp f

  private module ZL = ZarLatUniversalProp

  private
    instance
      _ = R .snd

  D : CompactOpen (Sp ⟅ R ⟆)
  D = yonedaᴾ ZarLatFun R .inv (ZL.D R f)

  SpR[1/f]≅⟦Df⟧ : NatIso (Sp .F-ob R[1/ f ]AsCommRing) ⟦ D ⟧ᶜᵒ
  N-ob (trans SpR[1/f]≅⟦Df⟧) B φ = (φ ∘cr /1AsCommRingHom) , ∨lRid _ ∙ path
    where
    open CommRingHomTheory φ
    open IsSupport (ZL.isSupportD B)
    instance
      _ = B .snd
      _ = ZariskiLattice B .snd

    isUnitφ[f/1] : φ .fst (f /1) ∈ B ˣ
    isUnitφ[f/1] = RingHomRespInv (f /1) ⦃ S/1⊆S⁻¹Rˣ f ∣ 1 , sym (·IdR f) ∣₁ ⦄

    path : ZL.D B (φ .fst (f /1)) ≡ 1l
    path = supportUnit _ isUnitφ[f/1]

  N-hom (trans SpR[1/f]≅⟦Df⟧) _ = funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) (CommRingHom≡ refl)

  inv (nIso SpR[1/f]≅⟦Df⟧ B) (φ , Dφf≡D1) = invElemUniversalProp B φ isUnitφf .fst .fst
    where
    instance _ = ZariskiLattice B .snd
    isUnitφf : φ .fst f ∈ B ˣ
    isUnitφf = unitLemmaZarLat B (φ $cr f) (sym (∨lRid _) ∙ Dφf≡D1)

  sec (nIso SpR[1/f]≅⟦Df⟧ B) =
    funExt λ _ → Σ≡Prop (λ _ → squash/ _ _) (CommRingHom≡ (invElemUniversalProp _ _ _ .fst .snd))
  ret (nIso SpR[1/f]≅⟦Df⟧ B) =
    funExt λ φ → cong fst (invElemUniversalProp B (φ ∘cr /1AsCommRingHom) _ .snd (φ , refl))

  isAffineD : isAffineCompactOpen D
  isAffineD = ∣ R[1/ f ]AsCommRing , SpR[1/f]≅⟦Df⟧ ∣₁


-- compact opens of affine schemes are qcqs-schemes
module _ {ℓ : Level} (R : CommRing ℓ) (W : CompactOpen (Sp ⟅ R ⟆)) where

  open StandardOpens

  open Iso
  open Functor
  open NatTrans
  open NatIso
  open isIsoC
  open DistLatticeStr ⦃...⦄
  open CommRingStr ⦃...⦄
  open PosetStr ⦃...⦄
  open IsCommRingHom
  open IsLatticeHom
  open ZarLat

  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice (CompOpenDistLattice .F-ob (Sp .F-ob R)))) using (IndPoset; ind≤bigOp)
  open InvertingElementsBase R
  open Join
  open JoinMap
  open AffineCover
  private module ZL = ZarLatUniversalProp

  private
    instance
      _ = R .snd
      _ = ZariskiLattice R .snd
      _ = CompOpenDistLattice .F-ob (Sp .F-ob R) .snd
      _ = CompOpenDistLattice .F-ob ⟦ W ⟧ᶜᵒ .snd
      _ = IndPoset .snd

    w : ZL R
    w = yonedaᴾ ZarLatFun R .fun W

    -- yoneda is a lattice homomorphsim
    isHomYoneda : IsLatticeHom (DistLattice→Lattice (ZariskiLattice R) .snd)
                               (yonedaᴾ ZarLatFun R .inv)
                               (DistLattice→Lattice (CompOpenDistLattice ⟅ Sp ⟅ R ⟆ ⟆) .snd)
    pres0 isHomYoneda = makeNatTransPath (funExt₂ (λ _ _ → refl))
    pres1 isHomYoneda =
      makeNatTransPath (funExt₂ (λ _ φ → inducedZarLatHom φ .snd .pres1))
    pres∨l isHomYoneda u v =
      makeNatTransPath (funExt₂ (λ _ φ → inducedZarLatHom φ .snd .pres∨l u v))
    pres∧l isHomYoneda u v =
      makeNatTransPath (funExt₂ (λ _ φ → inducedZarLatHom φ .snd .pres∧l u v))

    module _ {n : ℕ}
             (f : FinVec (fst R) n)
             (⋁Df≡W : ⋁ (CompOpenDistLattice ⟅ Sp ⟅ R ⟆ ⟆) (D R ∘ f) ≡ W) where

      Df≤W : ∀ i → D R (f i) ≤ W
      Df≤W i = subst (D R (f i) ≤_) ⋁Df≡W (ind≤bigOp (D R ∘ f) i)

      toAffineCover : AffineCover ⟦ W ⟧ᶜᵒ
      AffineCover.n toAffineCover = n
      U toAffineCover i = compOpenDownHom (Sp ⟅ R ⟆) W .fst (D R (f i))
      covers toAffineCover = sym (pres⋁ (compOpenDownHom (Sp ⟅ R ⟆) W) (D R ∘ f))
                           ∙ cong (compOpenDownHom (Sp ⟅ R ⟆) W .fst) ⋁Df≡W
                           ∙ makeNatTransPath (funExt₂ (λ _ → snd))
      isAffineU toAffineCover i =
        ∣ _ , seqNatIso (SpR[1/f]≅⟦Df⟧ R (f i)) (compOpenDownHomNatIso _ (Df≤W i)) ∣₁

  module _ {n : ℕ}
           (f : FinVec (fst R) n)
           (⋁Df≡w : ⋁ (ZariskiLattice R) (ZL.D R ∘ f) ≡ w) where

    private
      ⋁Df≡W : ⋁ (CompOpenDistLattice ⟅ Sp ⟅ R ⟆ ⟆) (D R ∘ f) ≡ W
      ⋁Df≡W = sym (pres⋁ (_ , isHomYoneda) (ZL.D R ∘ f))
            ∙ cong (yonedaᴾ ZarLatFun R .inv) ⋁Df≡w
            ∙ yonedaᴾ ZarLatFun R .leftInv W

    makeAffineCoverCompOpenOfAffine : AffineCover ⟦ W ⟧ᶜᵒ
    makeAffineCoverCompOpenOfAffine = toAffineCover f ⋁Df≡W

  hasAffineCoverCompOpenOfAffine : hasAffineCover ⟦ W ⟧ᶜᵒ
  hasAffineCoverCompOpenOfAffine = PT.map truncHelper ([]surjective w)
    where
    truncHelper : Σ[ n,f ∈ Σ ℕ (FinVec (fst R)) ] [ n,f ] ≡ w → AffineCover ⟦ W ⟧ᶜᵒ
    truncHelper ((n , f) , [n,f]≡w) = makeAffineCoverCompOpenOfAffine f (ZL.⋁D≡ R f ∙ [n,f]≡w)

  isQcQsSchemeCompOpenOfAffine : isQcQsScheme ⟦ W ⟧ᶜᵒ
  fst isQcQsSchemeCompOpenOfAffine = presLocalCompactOpen _ _ (isSubcanonicalZariskiCoverage R)
  snd isQcQsSchemeCompOpenOfAffine = hasAffineCoverCompOpenOfAffine
