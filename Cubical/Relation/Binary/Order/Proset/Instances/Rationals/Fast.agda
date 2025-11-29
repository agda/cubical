module Cubical.Relation.Binary.Order.Proset.Instances.Rationals.Fast where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Proset

open import Cubical.Relation.Binary.Order.Poset.Instances.Rationals.Fast

ℚ≤Proset : Proset ℓ-zero ℓ-zero
ℚ≤Proset = Poset→Proset ℚ≤Poset
