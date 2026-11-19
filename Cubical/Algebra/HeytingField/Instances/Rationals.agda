module Cubical.Algebra.HeytingField.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedField.Base
open import Cubical.Algebra.OrderedField.Instances.Rationals
open import Cubical.Algebra.HeytingField.Base

ℚHeytingField : HeytingField ℓ-zero ℓ-zero
ℚHeytingField = OrderedField→HeytingField ℚOrderedField
