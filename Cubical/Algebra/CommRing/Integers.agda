{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.CommRing.Integers where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.HITs.Ints.BiInvInt
  renaming (
    _+_ to _+ℤ_;
    -_ to _-ℤ_;
    +-assoc to +ℤ-assoc;
    +-comm to +ℤ-comm
  )

BiInvIntAsCommRing : CommRing {ℓ-zero}
BiInvIntAsCommRing =
  makeCommRing
    zero (suc zero) _+ℤ_ _·_ _-ℤ_
    isSetBiInvInt
    +ℤ-assoc +-zero +-invʳ +ℤ-comm
    ·-assoc ·-identityʳ
    (λ x y z → sym (·-distribˡ x y z))
    ·-comm
