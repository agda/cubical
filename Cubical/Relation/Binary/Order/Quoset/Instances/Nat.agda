module Cubical.Relation.Binary.Order.Quoset.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Relation.Binary.Order.StrictOrder.Instances.Nat

ℕ<Quoset : Quoset ℓ-zero ℓ-zero
ℕ<Quoset = StrictOrder→Quoset ℕ<StrictOrder
