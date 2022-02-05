{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Data.Nat.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Base

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

private
  variable
    l m n : ℕ

min : ℕ → ℕ → ℕ
min zero m = zero
min (suc n) zero = zero
min (suc n) (suc m) = suc (min n m)

minComm : (n m : ℕ) → min n m ≡ min m n
minComm zero zero = refl
minComm zero (suc m) = refl
minComm (suc n) zero = refl
minComm (suc n) (suc m) = cong suc (minComm n m)

max : ℕ → ℕ → ℕ
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

maxComm : (n m : ℕ) → max n m ≡ max m n
maxComm zero zero = refl
maxComm zero (suc m) = refl
maxComm (suc n) zero = refl
maxComm (suc n) (suc m) = cong suc (maxComm n m)

znots : ¬ (0 ≡ suc n)
znots eq = subst (caseNat ℕ ⊥) eq 0

snotz : ¬ (suc n ≡ 0)
snotz eq = subst (caseNat ⊥ ℕ) eq 0

injSuc : suc m ≡ suc n → m ≡ n
injSuc p = cong predℕ p

discreteℕ : Discrete ℕ
discreteℕ zero zero = yes refl
discreteℕ zero (suc n) = no znots
discreteℕ (suc m) zero = no snotz
discreteℕ (suc m) (suc n) with discreteℕ m n
... | yes p = yes (cong suc p)
... | no p = no (λ x → p (injSuc x))

isSetℕ : isSet ℕ
isSetℕ = Discrete→isSet discreteℕ

-- Arithmetic facts about predℕ

suc-predℕ : ∀ n → ¬ n ≡ 0 → n ≡ suc (predℕ n)
suc-predℕ zero p = ⊥.rec (p refl)
suc-predℕ (suc n) p = refl

-- Arithmetic facts about +

+-zero : ∀ m → m + 0 ≡ m
+-zero zero = refl
+-zero (suc m) = cong suc (+-zero m)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm m zero = +-zero m
+-comm m (suc n) = (+-suc m n) ∙ (cong suc (+-comm m n))

-- Addition is associative
+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc zero _ _    = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

inj-m+ : m + l ≡ m + n → l ≡ n
inj-m+ {zero} p = p
inj-m+ {suc m} p = inj-m+ (injSuc p)

inj-+m : l + m ≡ n + m → l ≡ n
inj-+m {l} {m} {n} p = inj-m+ ((+-comm m l) ∙ (p ∙ (+-comm n m)))

m+n≡n→m≡0 : m + n ≡ n → m ≡ 0
m+n≡n→m≡0 {n = zero} = λ p → (sym (+-zero _)) ∙ p
m+n≡n→m≡0 {n = suc n} p = m+n≡n→m≡0 (injSuc ((sym (+-suc _ n)) ∙ p))

m+n≡0→m≡0×n≡0 : m + n ≡ 0 → (m ≡ 0) × (n ≡ 0)
m+n≡0→m≡0×n≡0 {zero} = refl ,_
m+n≡0→m≡0×n≡0 {suc m} p = ⊥.rec (snotz p)

-- Arithmetic facts about ·

0≡m·0 : ∀ m → 0 ≡ m · 0
0≡m·0 zero = refl
0≡m·0 (suc m) = 0≡m·0 m

·-suc : ∀ m n → m · suc n ≡ m + m · n
·-suc zero n = refl
·-suc (suc m) n
  = cong suc
  ( n + m · suc n ≡⟨ cong (n +_) (·-suc m n) ⟩
    n + (m + m · n) ≡⟨ +-assoc n m (m · n) ⟩
    (n + m) + m · n ≡⟨ cong (_+ m · n) (+-comm n m) ⟩
    (m + n) + m · n ≡⟨ sym (+-assoc m n (m · n)) ⟩
    m + (n + m · n) ∎
  )

·-comm : ∀ m n → m · n ≡ n · m
·-comm zero n = 0≡m·0 n
·-comm (suc m) n = cong (n +_) (·-comm m n) ∙ sym (·-suc n m)

·-distribʳ : ∀ m n o → (m · o) + (n · o) ≡ (m + n) · o
·-distribʳ zero _ _ = refl
·-distribʳ (suc m) n o = sym (+-assoc o (m · o) (n · o)) ∙ cong (o +_) (·-distribʳ m n o)

·-distribˡ : ∀ o m n → (o · m) + (o · n) ≡ o · (m + n)
·-distribˡ o m n = (λ i → ·-comm o m i + ·-comm o n i) ∙ ·-distribʳ m n o ∙ ·-comm (m + n) o

·-assoc : ∀ m n o → m · (n · o) ≡ (m · n) · o
·-assoc zero _ _ = refl
·-assoc (suc m) n o = cong (n · o +_) (·-assoc m n o) ∙ ·-distribʳ n (m · n) o

·-identityˡ : ∀ m → 1 · m ≡ m
·-identityˡ m = +-zero m

·-identityʳ : ∀ m → m · 1 ≡ m
·-identityʳ zero = refl
·-identityʳ (suc m) = cong suc (·-identityʳ m)

0≡n·sm→0≡n : 0 ≡ n · suc m → 0 ≡ n
0≡n·sm→0≡n {n = zero} p = refl
0≡n·sm→0≡n {n = suc n} p = ⊥.rec (znots p)

inj-·sm : l · suc m ≡ n · suc m → l ≡ n
inj-·sm {zero} {m} {n} p = 0≡n·sm→0≡n p
inj-·sm {l} {m} {zero} p = sym (0≡n·sm→0≡n (sym p))
inj-·sm {suc l} {m} {suc n} p = cong suc (inj-·sm (inj-m+ {m = suc m} p))

inj-sm· : suc m · l ≡ suc m · n → l ≡ n
inj-sm· {m} {l} {n} p = inj-·sm (·-comm l (suc m) ∙ p ∙ ·-comm (suc m) n)

-- Arithmetic facts about ∸

zero∸ : ∀ n → zero ∸ n ≡ zero
zero∸ zero = refl
zero∸ (suc _) = refl


n∸n : (n : ℕ) → n ∸ n ≡ 0
n∸n zero = refl
n∸n (suc n) = n∸n n

∸-cancelˡ : ∀ k m n → (k + m) ∸ (k + n) ≡ m ∸ n
∸-cancelˡ zero    = λ _ _ → refl
∸-cancelˡ (suc k) = ∸-cancelˡ k

+∸ : ∀ k n → (k + n) ∸ n ≡ k
+∸ zero n = n∸n n
+∸ (suc k) zero = cong suc (+-comm k zero)
+∸ (suc k) (suc n) = cong (_∸ n) (+-suc k n) ∙ +∸ (suc k) n

∸-cancelʳ : ∀ m n k → (m + k) ∸ (n + k) ≡ m ∸ n
∸-cancelʳ m n k = (λ i → +-comm m k i ∸ +-comm n k i) ∙ ∸-cancelˡ k m n

∸-distribʳ : ∀ m n k → (m ∸ n) · k ≡ m · k ∸ n · k
∸-distribʳ m       zero    k = refl
∸-distribʳ zero    (suc n) k = sym (zero∸ (k + n · k))
∸-distribʳ (suc m) (suc n) k = ∸-distribʳ m n k ∙ sym (∸-cancelˡ k (m · k) (n · k))



-- factorial:
_! : ℕ → ℕ
zero ! = 1
suc n ! = (suc n) · (n !)

--binomial coefficient:
_choose_ : ℕ → ℕ → ℕ
n choose zero = 1
zero choose suc k = 0
suc n choose suc k = n choose (suc k) + n choose k

evenOrOdd : (n : ℕ) → isEvenT n ⊎ isOddT n
evenOrOdd zero = inl tt
evenOrOdd (suc zero) = inr tt
evenOrOdd (suc (suc n)) = evenOrOdd n

¬evenAndOdd : (n : ℕ) → ¬ isEvenT n × isOddT n
¬evenAndOdd zero (p , ())
¬evenAndOdd (suc zero) ()
¬evenAndOdd (suc (suc n)) = ¬evenAndOdd n

isPropIsEvenT : (n : ℕ) → isProp (isEvenT n)
isPropIsEvenT zero x y = refl
isPropIsEvenT (suc zero) = isProp⊥
isPropIsEvenT (suc (suc n)) = isPropIsEvenT n

isPropIsOddT : (n : ℕ) → isProp (isOddT n)
isPropIsOddT n = isPropIsEvenT (suc n)

isPropEvenOrOdd : (n : ℕ) → isProp (isEvenT n ⊎ isOddT n)
isPropEvenOrOdd n (inl x) (inl x₁) = cong inl (isPropIsEvenT n x x₁)
isPropEvenOrOdd n (inl x) (inr x₁) = ⊥.rec (¬evenAndOdd n (x , x₁))
isPropEvenOrOdd n (inr x) (inl x₁) = ⊥.rec (¬evenAndOdd (suc n) (x , x₁))
isPropEvenOrOdd n (inr x) (inr x₁) = cong inr (isPropIsEvenT (suc n) x x₁)
