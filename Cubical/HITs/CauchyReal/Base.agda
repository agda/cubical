{-# OPTIONS --safe #-}
module Cubical.HITs.CauchyReal.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Order
open import Cubical.Data.Rationals.Properties
open import Cubical.Data.PositiveRational.Base

-- Higher inductive-inductive construction of Cauchy real, as in the HoTT book.

data ℝ : Type₀
record Cℝ : Type₀
data close : ℚ₊ → ℝ → ℝ → Type₀
syntax close ε x y = x ~[ ε ] y

-- Cauchy real
data ℝ where
  rat : ℚ → ℝ
  lim : ∀ (x : Cℝ) → ℝ
  eqℝ : ∀ (u v : ℝ) → (∀ ε → u ~[ ε ] v) → u ≡ v

-- Cauchy approximation
record Cℝ where
  inductive
  constructor mkCℝ
  field
    approx : ℚ₊ → ℝ
    isCauchy : ∀ (δ ε : ℚ₊) → approx δ ~[ δ +₊ ε ] approx ε

open Cℝ public

-- ε-closeness
data close where
  rat~rat : ∀ q r ε     → - (ε .value) < q - r → q - r < ε .value → rat q ~[ ε           ] rat r
  rat~lim : ∀ q y ε η   → rat q       ~[ ε ] y .approx η          → rat q ~[ ε +₊ η      ] lim y
  lim~rat : ∀ x r ε δ   → x .approx δ ~[ ε ] rat r                → lim x ~[ ε +₊ δ      ] rat r
  lim~lim : ∀ x y ε δ η → x .approx δ ~[ ε ] y .approx η          → lim x ~[ ε +₊ δ +₊ η ] lim y
  squash~ : ∀ u v ε (ξ ζ : u ~[ ε ] v) → ξ ≡ ζ

