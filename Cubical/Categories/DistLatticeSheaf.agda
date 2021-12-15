{-# OPTIONS --safe #-}
module Cubical.Categories.DistLatticeSheaf where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Poset

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Instances.Poset
open import Cubical.Categories.Instances.Semilattice
open import Cubical.Categories.Instances.Lattice
open import Cubical.Categories.Instances.DistLattice

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (L : DistLattice ℓ) (C : Category ℓ' ℓ'') (T : Terminal C) where
  open Category

  𝟙 : C .ob
  𝟙 = terminalOb C T

  DLCat : Category ℓ ℓ
  DLCat = DistLatticeCategory L

  -- C-valued presheaves on a distributive lattice
  DLPreSheaf : Category (ℓ-max (ℓ-max ℓ ℓ) (ℓ-max ℓ' ℓ'')) (ℓ-max (ℓ-max ℓ ℓ) ℓ'')
  DLPreSheaf = FUNCTOR (DLCat ^op) C

  isSheaf : (F : DLPreSheaf .ob) → {!!}
  isSheaf F = {!!}
