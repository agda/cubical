module Cubical.Algebra.DirectSum.DirectSumFun.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.AbGroup

private variable
  ℓ : Level

open AbGroupStr

-----------------------------------------------------------------------------
-- Definition

AlmostNullProof : (G : ℕ → Type ℓ) → (Gstr : (n : ℕ) → AbGroupStr (G n))
                  → (f : (n : ℕ) → G n) → (k : ℕ) → Type ℓ
AlmostNullProof G Gstr f k = (n : ℕ) → k < n → f n ≡ 0g (Gstr n)

AlmostNull : (G : ℕ → Type ℓ) → (Gstr : (n : ℕ) → AbGroupStr (G n))
             → (f : (n : ℕ) → G n) → Type ℓ
AlmostNull G Gstr f = Σ[ k ∈ ℕ ] AlmostNullProof G Gstr f k

AlmostNullP : (G : ℕ → Type ℓ) → (Gstr : (n : ℕ) → AbGroupStr (G n))
             → (f : (n : ℕ) → G n) → Type ℓ
AlmostNullP G Gstr f = ∥ (AlmostNull G Gstr f) ∥₁

⊕Fun : (G : ℕ → Type ℓ) → (Gstr : (n : ℕ) → AbGroupStr (G n)) → Type ℓ
⊕Fun G Gstr = Σ[ f ∈ ((n : ℕ) → G n) ] AlmostNullP G Gstr f
