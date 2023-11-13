{-# OPTIONS --safe #-}

module Cubical.Data.Fin.Recursive.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty hiding (rec; elim)
open import Cubical.Data.Nat hiding (elim)

data FinF (X : Type₀) : Type₀ where
  zero : FinF X
  suc : X → FinF X

Fin : ℕ → Type₀
Fin zero = ⊥
Fin (suc k) = FinF (Fin k)

private
  variable
    ℓ : Level
    k : ℕ
    R : Type ℓ

rec : R → (R → R) → Fin k → R
rec {k = suc k} z _ zero = z
rec {k = suc k} z s (suc x) = s (rec z s x)

elim
  : ∀(P : ∀{k} → Fin k → Type ℓ)
  → (∀{k} → P {suc k} zero)
  → (∀{k} (fn : Fin k) → P fn → P {suc k} (suc fn))
  → (fn : Fin k) → P fn
elim {k = suc k} P fz fs zero = fz
elim {k = suc k} P fz fs (suc x) = fs x (elim P fz fs x)

toℕ : Fin k → ℕ
toℕ {suc k}   zero  = zero
toℕ {suc k} (suc n) = suc (toℕ n)
