-- It is recommended to use Cubical.Algebra.CommRing.Instances.Int
-- instead of this file.

module Cubical.Algebra.CommRing.Instances.BiInvInt where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Int.MoreInts.BiInvInt
  renaming (
    _+_ to _+ℤ_;
    -_ to _-ℤ_;
    +-assoc to +ℤ-assoc;
    +-comm to +ℤ-comm
  )

BiInvℤAsCommRing : CommRing ℓ-zero
BiInvℤAsCommRing =
  makeCommRing
    zero (suc zero) _+ℤ_ _·_ _-ℤ_
    isSetBiInvℤ
    +ℤ-assoc +-zero +-invʳ +ℤ-comm
    ·-assoc ·-identityʳ
    (λ x y z → sym (·-distribˡ x y z))
    ·-comm
