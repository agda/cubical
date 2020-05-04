{-# OPTIONS --cubical --safe #-}
module Cubical.Data.FinData.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary

data Fin : ℕ → Type₀ where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero    = 0
toℕ (suc i) = suc (toℕ i)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero    = zero
fromℕ (suc n) = suc (fromℕ n)

¬Fin0 : ¬ Fin 0
¬Fin0 ()
