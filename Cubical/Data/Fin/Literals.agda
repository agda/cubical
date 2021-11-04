{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Data.Fin.Literals where

open import Agda.Builtin.Nat
  using (suc)
open import Agda.Builtin.FromNat
  renaming (Number to HasFromNat)
open import Cubical.Data.Fin.Base
  using (Fin; fromℕ≤)
open import Cubical.Data.Nat.Order.Recursive
  using (_≤_)

instance
  fromNatFin : {n : _} → HasFromNat (Fin (suc n))
  fromNatFin {n} = record
    { Constraint = λ m → m ≤ n
    ; fromNat    = λ m ⦃ m≤n ⦄ → fromℕ≤ m n m≤n
    }
