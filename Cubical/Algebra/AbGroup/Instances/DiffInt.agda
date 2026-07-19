-- It is recommended to use Cubical.Algebra.CommRing.Instances.Int
-- instead of this file.

module Cubical.Algebra.AbGroup.Instances.DiffInt where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Data.Int.MoreInts.DiffInt
  renaming (
    _+_ to _+ℤ_
  )

DiffℤasAbGroup : AbGroup ℓ-zero
DiffℤasAbGroup = makeAbGroup {G = ℤ}
                             [ (0 , 0) ]
                             _+ℤ_
                             -ℤ_
                             ℤ-isSet
                             +ℤ-assoc
                             (λ x → zero-identityʳ 0 x)
                             (λ x → -ℤ-invʳ x)
                             +ℤ-comm
