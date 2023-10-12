{-

   The impredicative way to do the functor of points of qcqs-schemes
   (over Spec(ℤ))

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Instances.ZFunctors where

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
open import Cubical.Data.Int as Int
  renaming ( ℤ to ℤ ; _+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_)


open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommRing.Instances.Unit
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Unit
open import Cubical.Algebra.ZariskiLattice.Base
open import Cubical.Algebra.ZariskiLattice.UniversalProperty

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.CommAlgebras
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Yoneda


open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ hiding ([_])

open Category hiding (_∘_) renaming (_⋆_ to _⋆c_)
open CommAlgebraHoms
-- open Cospan
-- open Pullback

private
 variable
  ℓ' ℓ'' : Level

-- TODO generalize level
--module _ {ℓ : Level} where

-- using the naming conventions of Nieper-Wisskirchen
ℤFunctor = Functor (CommRingsCategory {ℓ = ℓ-zero}) (SET ℓ-zero)
ℤFUNCTOR = FUNCTOR (CommRingsCategory {ℓ = ℓ-zero}) (SET ℓ-zero)

-- Yoneda in the notation of Demazure-Gabriel
-- uses that double op is original category definitionally
Sp : Functor (CommRingsCategory {ℓ = ℓ-zero} ^op) ℤFUNCTOR
Sp = YO {C = (CommRingsCategory {ℓ = ℓ-zero} ^op)}

-- special functors to talk about schemes
open Functor
open ZarLat

-- the Zariski lattice classifying compact open subobjects
𝓛 : ℤFunctor
F-ob 𝓛 A = ZL A , SQ.squash/
F-hom 𝓛 φ = inducedZarLatHom φ .fst
F-id 𝓛 {A} = cong fst (inducedZarLatHomId A)
F-seq 𝓛 φ ψ = cong fst (inducedZarLatHomSeq φ ψ)

-- the forgetful functor
-- aka the representable of ℤ[x]
-- aka the affine line
open Construction ℤCommRing
private
  ℤ[x] : CommRing ℓ-zero
  ℤ[x] = CommAlgebra→CommRing (ℤCommRing [ Unit ])

𝔸¹ : ℤFunctor
𝔸¹ = Sp .F-ob ℤ[x]


-- the big lattice of compact opens
CompactOpen : ℤFunctor → Type₁
CompactOpen X = X ⇒ 𝓛

open NatTrans
open ZarLatUniversalProp
open CommRingStr ⦃...⦄
-- the induced subfunctor
coSubfun : {X : ℤFunctor} (U : CompactOpen X)
         → ℤFunctor
F-ob (coSubfun {X = X} U) A = let instance _ = snd A in
    (Σ[ x ∈ X .F-ob A .fst  ] U .N-ob A x ≡ D A 1r)
  , isSetΣSndProp (X .F-ob A .snd) λ _ → squash/ _ _
F-hom (coSubfun {X = X} U) = {!!}
F-id (coSubfun {X = X} U) = {!!}
F-seq (coSubfun {X = X} U) = {!!}

-- the global sections functor
Γ : Functor ℤFUNCTOR (CommRingsCategory {ℓ-suc ℓ-zero})
fst (F-ob Γ X) = X ⇒ 𝔸¹
snd (F-ob Γ X) = {!!}
F-hom Γ = {!!}
F-id Γ = {!!}
F-seq Γ = {!!}


-- we get an adjunction modulo size issues
-- ΓSpOb : (A : CommRing ℓ)
