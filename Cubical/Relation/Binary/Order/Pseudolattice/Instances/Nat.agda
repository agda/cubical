module Cubical.Relation.Binary.Order.Pseudolattice.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤ℕ_)

open import Cubical.Relation.Binary.Order.Poset.Instances.Nat
open import Cubical.Relation.Binary.Order.Pseudolattice

ℕ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℕ≤Pseudolattice = makePseudolatticeFromPoset ℕ≤Poset min max
  min-≤-left
  (λ {a b} → min-≤-right {a} {b})
  minGLB
  left-≤-max
  (λ {a b} → right-≤-max {b} {a})
  maxLUB
