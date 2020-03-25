{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.NatMinusOne.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusOne.Base

-1+Path : ℕ ≡ ℕ₋₁
-1+Path = isoToPath (iso -1+_ 1+_ (λ _ → refl) (λ _ → refl))
