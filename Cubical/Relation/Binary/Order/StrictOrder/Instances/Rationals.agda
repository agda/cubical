module Cubical.Relation.Binary.Order.StrictOrder.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Loset

open import Cubical.Relation.Binary.Order.Loset.Instances.Rationals

ℚ<StrictOrder : StrictOrder ℓ-zero ℓ-zero
ℚ<StrictOrder = Loset→StrictOrder ℚ<Loset
