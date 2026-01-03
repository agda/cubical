{-# OPTIONS --no-exact-split #-}
module Cubical.Data.Fin.Literals where

open import Agda.Builtin.Nat
  using (suc)
open import Agda.Builtin.FromNat
  renaming (Number to HasFromNat)
open import Cubical.Data.Fin.Base
  using (Fin; fromℕ≤ᵗ)
open import Cubical.Data.Nat.Order.Inductive
  using (_≤ᵗ_)

instance
  fromNatFin : {n : _} → HasFromNat (Fin (suc n))
  fromNatFin {n} = record
    { Constraint = λ m → m ≤ᵗ n
    ; fromNat    = λ m ⦃ m≤n ⦄ → fromℕ≤ᵗ m n m≤n
    }
