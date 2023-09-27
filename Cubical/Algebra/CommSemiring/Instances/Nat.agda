{-# OPTIONS --safe #-}
module Cubical.Algebra.CommSemiring.Instances.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

import Cubical.Data.Nat as Nat

open import Cubical.Algebra.CommSemiring

ℕasCSR : CommSemiring ℓ-zero
ℕasCSR .fst  = Nat.ℕ
ℕasCSR .snd  = str
  where open CommSemiringStr

        str : CommSemiringStr Nat.ℕ
        0r str = Nat.zero
        1r str = Nat.suc Nat.zero
        _+_ str = Nat._+_
        _·_ str = Nat._·_
        isCommSemiring str =
          makeIsCommSemiring
            Nat.isSetℕ
            Nat.+-assoc Nat.+-zero Nat.+-comm
            Nat.·-assoc Nat.·-identityʳ
            (λ x y z → sym (Nat.·-distribˡ x y z))
            (λ _ → refl)
            Nat.·-comm
