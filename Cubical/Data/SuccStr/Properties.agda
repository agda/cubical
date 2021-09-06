{-# OPTIONS --safe #-}
module Cubical.Data.SuccStr.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.SuccStr.Base
open import Cubical.Data.Graph
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Empty

private
  variable
    ℓ ℓ′ : Level

ℕ+AsGraph : Graph ℓ-zero ℓ-zero
Obj ℕ+AsGraph = ℕ
Hom ℕ+AsGraph n k = Homs n k
    where
        Homs : ℕ → ℕ → Type ℓ-zero
        Homs zero k = Unit
        Homs (suc n) zero = ⊥
        Homs (suc n) (suc k) = Homs n k
