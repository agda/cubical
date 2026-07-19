module Cubical.Data.NatPlusOne.MoreNats.AssocNat.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.NatPlusOne.MoreNats.AssocNat.Base
open import Cubical.Data.NatPlusOne renaming (ℕ₊₁ to Nat; one to one'; _+₁_ to _+₁'_)

Nat→ℕ₊₁ : Nat → ℕ₊₁
Nat→ℕ₊₁ one' = 1
Nat→ℕ₊₁ (2+ n) = 1 +₁ Nat→ℕ₊₁ (1+ n)

ℕ₊₁→Nat : ℕ₊₁ → Nat
ℕ₊₁→Nat one = 1
ℕ₊₁→Nat (a +₁ b) = ℕ₊₁→Nat a +₁' ℕ₊₁→Nat b
ℕ₊₁→Nat (assoc a b c i) = +₁-assoc (ℕ₊₁→Nat a) (ℕ₊₁→Nat b) (ℕ₊₁→Nat c) i
ℕ₊₁→Nat (trunc m n p q i j) =
  1+ (isSetℕ _ _ (λ k → -1+ (ℕ₊₁→Nat (p k))) (λ k → -1+ (ℕ₊₁→Nat (q k))) i j)

ℕ₊₁→Nat→ℕ₊₁ : ∀ n → ℕ₊₁→Nat (Nat→ℕ₊₁ n) ≡ n
ℕ₊₁→Nat→ℕ₊₁ one' = refl
ℕ₊₁→Nat→ℕ₊₁ (2+ n) = cong (1+_ ∘ suc ∘ -1+_) (ℕ₊₁→Nat→ℕ₊₁ (1+ n))

private
  Nat→ℕ₊₁-+ : ∀ a b → Nat→ℕ₊₁ (a +₁' b) ≡ Nat→ℕ₊₁ a +₁ Nat→ℕ₊₁ b
  Nat→ℕ₊₁-+ one' b = refl
  Nat→ℕ₊₁-+ (2+ a) b = cong (one +₁_) (Nat→ℕ₊₁-+ (1+ a) b)
    ∙ assoc one (Nat→ℕ₊₁ (1+ a)) (Nat→ℕ₊₁ b)

Nat→ℕ₊₁→Nat : ∀ n → Nat→ℕ₊₁ (ℕ₊₁→Nat n) ≡ n
Nat→ℕ₊₁→Nat = ElimProp.f (trunc _ _) (λ i → one)
  λ {a} {b} m n → Nat→ℕ₊₁-+ (ℕ₊₁→Nat a) (ℕ₊₁→Nat b) ∙ (λ i → m i +₁ n i)

ℕ₊₁≡Nat : ℕ₊₁ ≡ Nat
ℕ₊₁≡Nat = isoToPath (iso ℕ₊₁→Nat Nat→ℕ₊₁ ℕ₊₁→Nat→ℕ₊₁ Nat→ℕ₊₁→Nat)
