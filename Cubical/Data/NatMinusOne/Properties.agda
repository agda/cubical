{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Data.NatMinusOne.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusOne.Base
open import Cubical.Reflection.StrictEquiv

-1+Path : ℕ ≡ ℕ₋₁
-1+Path = ua e
  where
  unquoteDecl e = declStrictEquiv e -1+_ 1+_
