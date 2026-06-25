module Cubical.Relation.Binary.Order.StrictOrder.Instances.Fast.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Loset

open import Cubical.Relation.Binary.Order.Loset.Instances.Fast.Int

ℤ<StrictOrder : StrictOrder ℓ-zero ℓ-zero
ℤ<StrictOrder = Loset→StrictOrder ℤ<Loset
