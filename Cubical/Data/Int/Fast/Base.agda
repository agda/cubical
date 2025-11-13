module Cubical.Data.Int.Fast.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat as ℕ hiding (_+_ ; _·_)
open import Cubical.Data.Int.Base hiding (_ℕ-_ ; _+_ ; _-_ ; _·_) public

infixl 7 _·_
infixl 6 _+_ _-_

ℕ-hlp : ℕ → ℕ → ℤ
ℕ-hlp m-n@zero n-m = - (pos n-m)
ℕ-hlp m-n@(suc _) n-m = pos m-n

_ℕ-_ : ℕ → ℕ → ℤ
m ℕ- n = ℕ-hlp (m ℕ.∸ n) (n ℕ.∸ m)

_+_ : ℤ → ℤ → ℤ
pos n + pos n₁ = pos (n ℕ.+ n₁)
negsuc n + negsuc n₁ = negsuc (suc (n ℕ.+ n₁))
pos n + negsuc n₁ = n ℕ- (suc n₁)
negsuc n + pos n₁ = n₁ ℕ- (suc n)

_-_ : ℤ → ℤ → ℤ
m - n = m + (- n)

_·_ : ℤ → ℤ → ℤ
pos n · pos n₁ = pos (n ℕ.· n₁)
pos zero · negsuc n₁ = pos zero
pos (suc n) · negsuc n₁ = negsuc (predℕ (suc n ℕ.· suc n₁))
negsuc n · pos zero = pos zero
negsuc n · pos (suc n₁) = negsuc (predℕ (suc n ℕ.· suc n₁))
negsuc n · negsuc n₁ = pos (suc n ℕ.· suc n₁)
