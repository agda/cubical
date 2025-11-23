module Cubical.Relation.Binary.Order.Quoset.Instances.Int.Fast where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Relation.Binary.Order.StrictOrder.Instances.Int.Fast

ℤ<Quoset : Quoset ℓ-zero ℓ-zero
ℤ<Quoset = StrictOrder→Quoset ℤ<StrictOrder
