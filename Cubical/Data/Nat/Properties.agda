{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Nat.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.Empty
open import Cubical.Data.Prod.Base

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

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

private
  variable
    l m n : ℕ

znots : ¬ (0 ≡ suc n)
znots eq = subst (caseNat ℕ ⊥) eq 0

snotz : ¬ (suc n ≡ 0)
snotz eq = subst (caseNat ⊥ ℕ) eq 0

injSuc : suc m ≡ suc n → m ≡ n
injSuc p = cong predℕ p

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
m+n≡0→m≡0×n≡0 {suc m} p = ⊥-elim (snotz p)

discreteℕ : Discrete ℕ
discreteℕ zero zero = yes refl
discreteℕ zero (suc n) = no znots
discreteℕ (suc m) zero = no snotz
discreteℕ (suc m) (suc n) with discreteℕ m n
... | yes p = yes (cong suc p)
... | no p = no (λ x → p (injSuc x))

isSetℕ : isSet ℕ
isSetℕ = Discrete→isSet discreteℕ

0≡m*0 : ∀ m → 0 ≡ m * 0
0≡m*0 zero = refl
0≡m*0 (suc m) = 0≡m*0 m

*-suc : ∀ m n → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n
  = cong suc
  ( n + m * suc n ≡⟨ cong (n +_) (*-suc m n) ⟩
    n + (m + m * n) ≡⟨ +-assoc n m (m * n) ⟩
    (n + m) + m * n ≡⟨ cong (_+ m * n) (+-comm n m) ⟩
    (m + n) + m * n ≡⟨ sym (+-assoc m n (m * n)) ⟩
    m + (n + m * n) ∎
  )

*-comm : ∀ m n → m * n ≡ n * m
*-comm zero n = 0≡m*0 n
*-comm (suc m) n = cong (n +_) (*-comm m n) ∙ sym (*-suc n m)

0≡n*sm→0≡n : 0 ≡ n * suc m → 0 ≡ n
0≡n*sm→0≡n {n = zero} p = refl
0≡n*sm→0≡n {n = suc n} p = ⊥-elim (znots p)

inj-*sm : l * suc m ≡ n * suc m → l ≡ n
inj-*sm {zero} {m} {n} p = 0≡n*sm→0≡n p
inj-*sm {l} {m} {zero} p = sym (0≡n*sm→0≡n (sym p))
inj-*sm {suc l} {m} {suc n} p = cong suc (inj-*sm (inj-m+ {m = suc m} p))

inj-sm* : suc m * l ≡ suc m * n → l ≡ n
inj-sm* {m} {l} {n} p = inj-*sm (*-comm l (suc m) ∙ p ∙ *-comm (suc m) n)
