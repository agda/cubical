{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Categories.DistLatticeSheaf.Extension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order

open import Cubical.Relation.Binary.Poset

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis
open import Cubical.Algebra.DistLattice.BigOps

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Limits.RightKan
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.Poset
open import Cubical.Categories.Instances.Semilattice
open import Cubical.Categories.Instances.Lattice
open import Cubical.Categories.Instances.DistLattice


open import Cubical.Categories.DistLatticeSheaf.Diagram
open import Cubical.Categories.DistLatticeSheaf.Base

private
  variable
    ℓ ℓ' ℓ'' : Level


module PreSheafExtension (L : DistLattice ℓ) (C : Category ℓ' ℓ'')
                         (limitC : Limits {ℓ} {ℓ} C) (L' : ℙ (fst L)) where

 open Category
 open Functor
 open Cone
 open LimCone

 private
  DLCat = DistLatticeCategory L
  DLSubCat = ΣPropCat  DLCat L'
  DLPreSheaf = Functor (DLCat ^op) C
  DLSubPreSheaf = Functor (DLSubCat ^op) C

  i : Functor DLSubCat DLCat
  F-ob i = fst
  F-hom i f = f
  F-id i = refl
  F-seq i _ _ = refl

 DLRan : DLSubPreSheaf → DLPreSheaf
 DLRan = Ran limitC (i ^opF)

 module _ (isBasisL' : IsBasis L L') (F : DLSubPreSheaf) where
  open SheafOnBasis L C L' isBasisL'
  open Order (DistLattice→Lattice L)
  open DistLatticeStr (snd L)
  open Join L
  open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L))
  open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L))
      using (∧≤RCancel ; ∧≤LCancel ; ≤-∧Pres)
  open PosetStr (IndPoset .snd) hiding (_≤_)

  open condCone
  private
   F* = T* limitC (i ^opF) F

  coneLemma : ∀ (c : ob C) {n : ℕ} (α : FinVec (fst L) n) (α∈L' : ∀ i → α i ∈ L')
            → Cone (funcComp F (BDiag (λ i → α i , α∈L' i)) ) c → Cone (F* (⋁ α)) c
  coneLemma c α α∈L' cc = {!!}

  isDLSheafDLRan : isDLBasisSheaf F → isDLSheafPullback L C (DLRan F)
  fst (isDLSheafDLRan isSheafF) x = {!!} --must be a more elegant way to do this
   --   limArrow (limitC _ (F* 0l)) x (toCone x)
   -- , λ f → limArrowUnique (limitC _ (F* 0l)) x (toCone x) f {!!}
   -- where
   -- toCone : (y : ob C) → Cone (F* 0l) y
   -- coneOut (toCone y) ((u , u∈L') , 0≥u) = {!isSheafF (λ ()) 0∈L'  y!}
   --  where
   --  0≡u : 0l ≡ u
   --  0≡u = is-antisym _ _ (∨lLid _) 0≥u
   --  0∈L' : 0l ∈ L'
   --  0∈L' = subst-∈ L' (sym 0≡u) u∈L'
   -- coneOutCommutes (toCone y) = {!!}

  snd (isDLSheafDLRan isSheafF) = {!!}
