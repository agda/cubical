{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Data.NatPlusOne.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat
open import Cubical.Data.NatPlusOne.Base

open import Cubical.Reflection.StrictEquiv

1+Path : ℕ ≡ ℕ₊₁
1+Path = ua e
  where
  unquoteDecl e = declStrictEquiv e 1+_ -1+_

ℕ₊₁→ℕ-inj : ∀ {m n} → ℕ₊₁→ℕ m ≡ ℕ₊₁→ℕ n → m ≡ n
ℕ₊₁→ℕ-inj p i = 1+ (injSuc p i)

infixl 7 _·₊₁_

_·₊₁_ : ℕ₊₁ → ℕ₊₁ → ℕ₊₁
(1+ m) ·₊₁ (1+ n) = 1+ (n + m · (suc n))

private
  ℕ₊₁→ℕ-·₊₁-comm : ∀ m n → ℕ₊₁→ℕ (m ·₊₁ n) ≡ (ℕ₊₁→ℕ m) · (ℕ₊₁→ℕ n)
  ℕ₊₁→ℕ-·₊₁-comm (1+ m) (1+ n) = refl

·₊₁-comm : ∀ m n → m ·₊₁ n ≡ n ·₊₁ m
·₊₁-comm (1+ m) (1+ n) = cong 1+_ (injSuc (·-comm (suc m) (suc n)))

·₊₁-assoc : ∀ m n o → m ·₊₁ (n ·₊₁ o) ≡ m ·₊₁ n ·₊₁ o
·₊₁-assoc (1+ m) (1+ n) (1+ o) = cong 1+_ (injSuc (·-assoc (suc m) (suc n) (suc o)))

·₊₁-identityˡ : ∀ n → 1 ·₊₁ n ≡ n
·₊₁-identityˡ (1+ n) = cong 1+_ (injSuc (·-identityˡ (suc n)))

·₊₁-identityʳ : ∀ n → n ·₊₁ 1 ≡ n
·₊₁-identityʳ (1+ n) = cong 1+_ (injSuc (·-identityʳ (suc n)))
