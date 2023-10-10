{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Instances.FPAlgebrasSmall where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.FinData

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FPAlgebra
open import Cubical.Algebra.CommAlgebra.FPAlgebra.Instances
open import Cubical.Algebra.CommAlgebra.Instances.Unit
open import Cubical.Algebra.ZariskiLattice.Base
open import Cubical.Algebra.ZariskiLattice.UniversalProperty

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
-- open import Cubical.Categories.Limits.Terminal
-- open import Cubical.Categories.Limits.Pullback
-- open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.CommAlgebras
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Yoneda


open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ

open Category hiding (_∘_) renaming (_⋆_ to _⋆c_)
open CommAlgebraHoms
-- open Cospan
-- open Pullback

private
 variable
  ℓ ℓ' ℓ'' : Level


module _ (R : CommRing ℓ) where
  open Category

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
  _⋆_ FPAlgebrasSmallCategory = compCommAlgebraHom _ _ _
  ⋆IdL FPAlgebrasSmallCategory = compIdCommAlgebraHom
  ⋆IdR FPAlgebrasSmallCategory = idCompCommAlgebraHom
  ⋆Assoc FPAlgebrasSmallCategory = compAssocCommAlgebraHom
  isSetHom FPAlgebrasSmallCategory = isSetAlgebraHom _ _


  -- yoneda in the notation of Demazure-Gabriel
  -- uses η-equality of Categories
  Sp : Functor (FPAlgebrasSmallCategory ^op) (FUNCTOR FPAlgebrasSmallCategory (SET ℓ))
  Sp = YO {C = (FPAlgebrasSmallCategory ^op)}

  open Functor

  -- special internal objects to talk about schemes
  -- first the affine line
  private
    R[x]ᶠᵖ : SmallFPAlgebra
    n R[x]ᶠᵖ = 1
    m R[x]ᶠᵖ = 0
    relations R[x]ᶠᵖ = λ ()

  𝔸¹ = Sp .F-ob R[x]ᶠᵖ

  -- the Zariski lattice (classifying compact open subobjects)
  𝓛 : Functor FPAlgebrasSmallCategory (SET ℓ)
  F-ob 𝓛 A = ZarLat.ZL (CommAlgebra→CommRing (indFPAlg A)) , SQ.squash/
  F-hom 𝓛  φ = inducedZarLatHom (CommAlgebraHom→CommRingHom _ _ φ) .fst
  F-id 𝓛 = {!!}
  F-seq 𝓛 = {!!}
