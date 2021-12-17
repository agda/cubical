{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Lattice where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Lattice

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Semilattice

open Category

LatticeCategory : ∀ {ℓ} (L : Lattice ℓ) → Category ℓ ℓ
LatticeCategory L = SemilatticeCategory (Lattice→MeetSemilattice L)
