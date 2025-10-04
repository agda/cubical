module Cubical.Relation.Binary.Order.Proset.Instances.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Proset

open import Cubical.Relation.Binary.Order.Poset.Instances.Int

ℤ≤Proset : Proset ℓ-zero ℓ-zero
ℤ≤Proset = Poset→Proset ℤ≤Poset
