module Cubical.Relation.Binary.Order.Quoset.Instances.Rationals.Fast where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Relation.Binary.Order.StrictOrder.Instances.Rationals.Fast

ℚ<Quoset : Quoset ℓ-zero ℓ-zero
ℚ<Quoset = StrictOrder→Quoset ℚ<StrictOrder
