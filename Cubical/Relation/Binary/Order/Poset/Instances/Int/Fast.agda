module Cubical.Relation.Binary.Order.Poset.Instances.Int.Fast where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Toset

open import Cubical.Relation.Binary.Order.Toset.Instances.Int.Fast

ℤ≤Poset : Poset ℓ-zero ℓ-zero
ℤ≤Poset = Toset→Poset ℤ≤Toset
