{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.CommRing.Integers where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing

module _ where
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

-- makeCommRing ? ? ? ? ? ? ? ? ? ? ? ? ? ?

module _ where
  open import Cubical.Data.Int

  IntAsCommRing : CommRing {ℓ-zero}
  IntAsCommRing = makeCommRing {R = Int} 0 1 _+_ _·_ -_ isSetInt
    +-assoc +-identityʳ +-inverseʳ +-comm (λ x y z → sym (·-assoc x y z)) ·-identityʳ
    (λ x y z → sym (·-distribˡ x y z)) ·-comm

module _ where
  open import Cubical.HITs.Ints.QuoInt
  
  QuoIntAsCommRing : CommRing {ℓ-zero}
  QuoIntAsCommRing = makeCommRing {R = ℤ} 0 1 _+_ _·_ -_ isSetℤ
    +-assoc +-identityʳ +-inverseʳ +-comm ·-assoc ·-identityʳ
    (λ x y z → sym (·-distribˡ x y z)) ·-comm
