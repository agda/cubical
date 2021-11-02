{-# OPTIONS --safe #-}
module Cubical.HITs.Sn.Base where

open import Cubical.HITs.Susp.Base
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Empty
open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.HITs.S1

S : ℕ₋₁ → Type₀
S neg1 = ⊥
S (ℕ→ℕ₋₁ n) = Susp (S (-1+ n))

S₊ : ℕ → Type₀
S₊ 0 = Bool
S₊ 1 = S¹
S₊ (suc (suc n)) = Susp (S₊ (suc n))

ptSn : (n : ℕ) → S₊ n
ptSn zero = true
ptSn (suc zero) = base
ptSn (suc (suc n)) = north

-- Pointed version
S₊∙ : (n : ℕ) → Pointed₀
S₊∙ n = (S₊ n) , ptSn n
