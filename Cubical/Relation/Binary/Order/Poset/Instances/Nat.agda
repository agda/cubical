module Cubical.Relation.Binary.Order.Poset.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Toset

open import Cubical.Relation.Binary.Order.Toset.Instances.Nat

ℕ≤Poset : Poset ℓ-zero ℓ-zero
ℕ≤Poset = Toset→Poset ℕ≤Toset
