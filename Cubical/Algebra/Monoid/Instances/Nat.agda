{-# OPTIONS --safe #-}
module Cubical.Algebra.Monoid.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat

open import Cubical.Algebra.Monoid


NatMonoid : Monoid ℓ-zero
fst NatMonoid = ℕ
MonoidStr.ε (snd NatMonoid) = 0
MonoidStr._·_ (snd NatMonoid) = _+_
MonoidStr.isMonoid (snd NatMonoid) = makeIsMonoid isSetℕ +-assoc +-zero (λ _ → refl)
