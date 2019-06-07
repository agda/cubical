{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Sn.Base where

open import Cubical.HITs.Susp
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Foundations.Prelude

S : ℕ → Type₀
S zero = ⊥
S (suc n) = Susp (S n)
