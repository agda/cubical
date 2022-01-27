{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Semilattice where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Semilattice

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Poset

open Category

module _ {ℓ} (L : Semilattice ℓ) where
  -- more convenient than working with meet-semilattices
  -- as joins are limits
  open JoinSemilattice L

  SemilatticeCategory : Category ℓ ℓ
  SemilatticeCategory = PosetCategory IndPoset
