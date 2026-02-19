module Cubical.Relation.Binary.Order.Pseudolattice.Instances.Fast.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Fast.Int
open import Cubical.Data.Fast.Int.Order renaming (_≤_ to _≤ℤ_)

open import Cubical.Relation.Binary.Order.Poset.Instances.Fast.Int
open import Cubical.Relation.Binary.Order.Pseudolattice

ℤ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℤ≤Pseudolattice = makePseudolatticeFromPoset ℤ≤Poset min max
  min≤
  (recompute≤ (subst (_≤ℤ _) (minComm _ _) min≤))
  (λ x≤a x≤b → recompute≤ (subst (_≤ℤ min _ _) (minIdem _) (≤MonotoneMin x≤a x≤b)))
  ≤max
  (recompute≤ (subst (_ ≤ℤ_) (maxComm _ _) ≤max))
  (λ a≤x b≤x → recompute≤ (subst (max _ _ ≤ℤ_) (maxIdem _) (≤MonotoneMax a≤x b≤x)))
