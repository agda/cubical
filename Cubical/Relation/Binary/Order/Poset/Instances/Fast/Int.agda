module Cubical.Relation.Binary.Order.Poset.Instances.Fast.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Toset

open import Cubical.Relation.Binary.Order.Toset.Instances.Fast.Int

ℤ≤Poset : Poset ℓ-zero ℓ-zero
ℤ≤Poset = Toset→Poset ℤ≤Toset
