{-

   A qcqs-scheme is a ℤ-functor that is a local (a Zariski-sheaf)
   and has an affine cover, where that notion of cover is given
   by the lattice structure of compact open subfunctors

-}

{-# OPTIONS --safe --lossy-unification #-}
module Cubical.AlgebraicGeometry.Functorial.ZFunctors.QcQsScheme where

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

open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.Base
open import Cubical.AlgebraicGeometry.Functorial.ZFunctors.CompactOpen

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.DistLattices
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Site.Cover
open import Cubical.Categories.Site.Coverage
open import Cubical.Categories.Site.Sheaf
open import Cubical.Categories.Site.Instances.ZariskiCommRing
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Yoneda


open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Binary.Order.Poset

open Category hiding (_∘_) renaming (_⋆_ to _⋆c_)

module _ {ℓ : Level} (X : ℤFunctor {ℓ = ℓ}) where
  open Functor
  open DistLatticeStr ⦃...⦄
  open Join (CompOpenDistLattice .F-ob X)
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice (CompOpenDistLattice .F-ob X)))
  private instance _ = (CompOpenDistLattice .F-ob X) .snd

  record AffineCover : Type (ℓ-suc ℓ) where
    field
      n : ℕ
      U : FinVec (CompactOpen X) n
      covers : ⋁ U ≡ 1l -- TODO: equivalent to X ≡ ⟦ ⋁ U ⟧ᶜᵒ
      isAffineU : ∀ i → isAffineCompactOpen (U i)

  hasAffineCover : Type (ℓ-suc ℓ)
  hasAffineCover = ∥ AffineCover ∥₁

  isQcQsScheme : Type (ℓ-suc ℓ)
  isQcQsScheme = isLocal X × hasAffineCover


-- affine schemes are qcqs-schemes
module _ {ℓ : Level} (A : CommRing ℓ) where
  open Functor
  open DistLatticeStr ⦃...⦄
  open AffineCover
  private instance _ = (CompOpenDistLattice .F-ob (Sp .F-ob A)) .snd

  -- the canonical one element affine cover of a representable
  singlAffineCover : AffineCover (Sp .F-ob A)
  n singlAffineCover = 1
  U singlAffineCover zero = 1l
  covers singlAffineCover = ∨lRid _
  isAffineU singlAffineCover zero = ∣ A , X≅⟦1⟧ (Sp .F-ob A) ∣₁

  isQcQsSchemeAffine : isQcQsScheme (Sp .F-ob A)
  fst isQcQsSchemeAffine = isSubcanonicalZariskiCoverage A
  snd isQcQsSchemeAffine = ∣ singlAffineCover ∣₁
