{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Semilattice where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Semilattice

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Poset

open Category


module _ {ℓ} (L : Semilattice ℓ) where
  open JoinSemilattice L

  JoinSemilatticeCategory : Category ℓ ℓ
  JoinSemilatticeCategory = PosetCategory IndPoset


module _ {ℓ} (L : Semilattice ℓ) where
  open MeetSemilattice L

  MeetSemilatticeCategory : Category ℓ ℓ
  MeetSemilatticeCategory = PosetCategory IndPoset
