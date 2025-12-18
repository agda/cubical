module Cubical.Relation.Binary.Order.Poset.Instances.Rationals.Fast where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Toset

open import Cubical.Relation.Binary.Order.Toset.Instances.Rationals.Fast

ℚ≤Poset : Poset ℓ-zero ℓ-zero
ℚ≤Poset = Toset→Poset ℚ≤Toset
