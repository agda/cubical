{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.DistLattice where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.DistLattice

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Lattice

open Category

DistLatticeCategory : ∀ {ℓ} (L : DistLattice ℓ) → Category ℓ ℓ
DistLatticeCategory L = LatticeCategory (DistLattice→Lattice L)
