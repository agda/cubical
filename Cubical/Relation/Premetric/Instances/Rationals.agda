module Cubical.Relation.Premetric.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.ArchimedeanField.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Instances.ArchimedeanField

open AFSpace

ℚPrSpace : PremetricSpace ℓ-zero ℓ-zero
ℚPrSpace = ArchimedeanField→PremetricSpace ℚArchimedeanField
