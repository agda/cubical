module Cubical.Relation.Binary.Order.Proset.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Proset

open import Cubical.Relation.Binary.Order.Poset.Instances.Nat

ℕ≤Proset : Proset ℓ-zero ℓ-zero
ℕ≤Proset = Poset→Proset ℕ≤Poset
