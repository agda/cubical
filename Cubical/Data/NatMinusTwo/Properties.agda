{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Data.NatMinusTwo.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusOne using (ℕ₋₁)
open import Cubical.Data.NatMinusTwo.Base

-2+Path : ℕ ≡ ℕ₋₂
-2+Path = isoToPath (iso -2+_ 2+_ (λ _ → refl) (λ _ → refl))
