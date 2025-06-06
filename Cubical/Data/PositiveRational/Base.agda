{-# OPTIONS --safe #-}
module Cubical.Data.PositiveRational.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Order
open import Cubical.Data.Rationals.Properties

record ℚ₊ : Type₀ where
  constructor rat₊
  field
    value : ℚ
    positive : value > 0

open ℚ₊ public

infixl 6 _+₊_

_+₊_ : ℚ₊ → ℚ₊ → ℚ₊
r +₊ s = rat₊
           (r .value + s .value)
           (<Monotone+ 0 (r .value) 0 (s .value) (r .positive) (s .positive))
