{-# OPTIONS --safe #-}
module Cubical.Algebra.CommSemiring.Instances.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ; suc; zero)

open import Cubical.Algebra.CommSemiring

ℕasCSR : CommSemiring ℓ-zero
ℕasCSR .fst  = ℕ
ℕasCSR .snd  = str
  where
    open CommSemiringStr

    str : CommSemiringStr ℕ
    0r str = zero
    1r str = suc zero
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
