module Cubical.Data.FinSequence.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Fin.Inductive.Base

private
  variable
    ℓ ℓ' : Level

record FinSequence (m : ℕ) (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor finsequence
  field
    fobj : Fin (suc m) → Type ℓ
    fmap : {n : Fin m} → fobj (injectSuc n) → fobj (fsuc n)

record FinSequenceMap {m : ℕ}
  (C : FinSequence m ℓ) (D : FinSequence m ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor finsequencemap
  field
    fmap : (n : Fin (suc m)) → FinSequence.fobj C n → FinSequence.fobj D n
    fcomm : (n : Fin m) (x : FinSequence.fobj C (injectSuc n))
      → FinSequence.fmap D (fmap (injectSuc n) x) ≡ fmap (fsuc n) (FinSequence.fmap C x)
