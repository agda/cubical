{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.DistLatticeSheaf.ComparisonLemma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; _+_)
open import Cubical.Data.Nat.Order hiding (_≤_)
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order
open import Cubical.Data.Sum

open import Cubical.Relation.Binary.Poset
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.DistLattice.Basis
open import Cubical.Algebra.DistLattice.BigOps

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.RightKan
open import Cubical.Categories.Instances.Poset
open import Cubical.Categories.Instances.Semilattice
open import Cubical.Categories.Instances.Lattice
open import Cubical.Categories.Instances.DistLattice
open import Cubical.Categories.Instances.Functors

open import Cubical.Categories.DistLatticeSheaf.Diagram
open import Cubical.Categories.DistLatticeSheaf.Base
open import Cubical.Categories.DistLatticeSheaf.Extension


private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (L : DistLattice ℓ) (C : Category ℓ' ℓ'') (limitC : Limits {ℓ} {ℓ} C)
         (B : ℙ (fst L)) (isBasisB : IsBasis L B) where


 open Category hiding (_∘_)
 open Functor
 open Cone
 open LimCone
 open SheafOnBasis L C B isBasisB

 private
  Lᵒᵖ = DistLatticeCategory L ^op
  Bᵒᵖ = ΣPropCat (DistLatticeCategory L) B ^op

  ShB = ΣPropCat (FUNCTOR Bᵒᵖ C) isDLBasisSheafProp
  ShL = ΣPropCat (FUNCTOR Lᵒᵖ C) (isDLSheafProp L C)

  i : Functor Bᵒᵖ Lᵒᵖ
  F-ob i = fst
  F-hom i f = f
  F-id i = refl
  F-seq i _ _ = refl

 restSh : Functor ShL ShB
 F-ob restSh (F , isShfF) = (F ∘F i) , isShfF∘i
   where
   isShfF∘i : isDLBasisSheaf (F ∘F i)
   isShfF∘i α ⋁α∈B = let
     β : FinVec (fst L) _
     β = λ i → α i .fst in {!isShfF _ _ β!}
 F-hom restSh = {!!}
 F-id restSh = {!!}
 F-seq restSh = {!!}
