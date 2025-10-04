module Cubical.Relation.Binary.Order.StrictOrder.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Loset

open import Cubical.Relation.Binary.Order.Loset.Instances.Nat

ℕ<StrictOrder : StrictOrder ℓ-zero ℓ-zero
ℕ<StrictOrder = Loset→StrictOrder ℕ<Loset
