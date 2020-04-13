{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Ints.HAEquivInt.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.HalfAdjoint


data HAEquivInt : Type₀ where
  zero : HAEquivInt
  suc : HAEquivInt -> HAEquivInt

  -- suc is a HAEquiv:
  pred : HAEquivInt -> HAEquivInt
  suc-pred : ∀ z -> suc (pred z) ≡ z
  pred-suc : ∀ z -> pred (suc z) ≡ z
  coh : ∀ z → (λ i → suc (pred-suc z i)) ≡ suc-pred (suc z)


suc-haequiv : HAEquiv HAEquivInt HAEquivInt
suc-haequiv = suc , record { g = pred ; sec = pred-suc ; ret = suc-pred ; com = coh }


-- OPEN: prove HAEquivInt ≃ Int! See Experiments/HInt.agda
