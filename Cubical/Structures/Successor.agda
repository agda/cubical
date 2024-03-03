{-# OPTIONS --safe #-}
{-
  Successor structures for spectra, chain complexes and fiber sequences.
  This is an idea from Floris van Doorn's phd thesis.
-}
module Cubical.Structures.Successor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order
open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level

record SuccStr (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Index : Type ℓ
    succ : Index → Index

open SuccStr

ℤ+ : SuccStr ℓ-zero
ℤ+ .Index = ℤ
ℤ+ .succ = sucℤ

ℕ+ : SuccStr ℓ-zero
ℕ+ .Index = ℕ
ℕ+ .succ = suc

Fin+ : (n : ℕ) → SuccStr ℓ-zero
Fin+ n .Index = Fin n
Fin+ n .succ (x , zero , p) = x , zero , p
Fin+ n .succ (x , suc diff , p) = suc x , diff , +-suc diff (suc x) ∙ p

record InjSuccStr (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    succStr : SuccStr ℓ
    semiInj : {i : Index succStr}
      → ¬ (succ succStr i ≡ succ succStr (succ succStr i))
      → ¬ (i ≡ succ succStr i)

open InjSuccStr

≠suc : {n : ℕ} → ¬ n ≡ suc n
≠suc {n = n} p = ¬m<m (subst (n <_) (sym p) (0 , refl))

ℕ+Inj : InjSuccStr ℓ-zero
succStr ℕ+Inj = ℕ+
semiInj ℕ+Inj {i = x} _ = ≠suc


Fin+Inj : ℕ → InjSuccStr ℓ-zero
succStr (Fin+Inj n) = Fin+ n
semiInj (Fin+Inj n) {i  = (x , zero , p)} a = a
semiInj (Fin+Inj n) {i = (x , suc diff , p)} q r =
  ¬m<m (subst (x <_) (sym (cong fst r)) (0 , refl))
