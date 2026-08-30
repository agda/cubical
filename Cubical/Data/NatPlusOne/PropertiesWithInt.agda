module Cubical.Data.NatPlusOne.PropertiesWithInt where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat renaming (NonZero to NonZeroℕ)
open import Cubical.Data.Int using (ℤ; pos; injPos; pos·pos; sucℤ; pos+)
  renaming (_·_ to _ℤ·_; _+_ to _ℤ+_)
open import Cubical.Data.NatPlusOne.Base
open import Cubical.Data.NatPlusOne.Properties

ℕ₊₁→ℤ : ℕ₊₁ → ℤ
ℕ₊₁→ℤ n = pos (ℕ₊₁→ℕ n)

ℕ₊₁→ℤ-inj : ∀{n}{n'} → ℕ₊₁→ℤ n ≡ ℕ₊₁→ℤ n' → n ≡ n'
ℕ₊₁→ℤ-inj {1+ n} {1+ n'} zz' = ℕ₊₁→ℕ-inj (injPos zz')

ℕ₊₁→ℤ-1+pred-def : ∀ (x : ℕ) → {{px : NonZeroℕ x}} →
  ℕ₊₁→ℤ (1+ predℕ x) ≡ pos x
ℕ₊₁→ℤ-1+pred-def (suc x) {{px}} = refl

·ℕ₊₁→ℤ-distr : ∀ n m → ℕ₊₁→ℤ (n ·₊₁ m) ≡ (ℕ₊₁→ℤ n) ℤ· (ℕ₊₁→ℤ m)
·ℕ₊₁→ℤ-distr n@(1+ n') m@(1+ m') = pos·pos (suc n') (suc m')

+ℕ₊₁→ℤ-distr : ∀ n m → ℕ₊₁→ℤ (n +₁ m) ≡ (ℕ₊₁→ℤ n) ℤ+ (ℕ₊₁→ℤ m)
+ℕ₊₁→ℤ-distr n@(1+ n') m@(1+ m') = cong sucℤ (pos+ (suc n') m')
