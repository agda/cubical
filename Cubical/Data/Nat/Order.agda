{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Nat.Order where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

open import Cubical.Data.Prod

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties

open import Cubical.Relation.Nullary

_≤_ : ℕ → ℕ → Set
m ≤ n = Σ[ k ∈ ℕ ] k + m ≡ n

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

data Trichotomy (m n : ℕ) : Set where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

private
  variable
    k l m n : ℕ

private
  witness-prop : ∀ j → isProp (j + m ≡ n)
  witness-prop {m} {n} j = isSetℕ (j + m) n

m≤n-isProp : isProp (m ≤ n)
m≤n-isProp {m} {n} (k , p) (l , q)
  = subtypeEquality witness-prop (k , p) (l , q) lemma
  where
  lemma : k ≡ l
  lemma = inj-+m (p ∙ (sym q))

zero-≤ : 0 ≤ n
zero-≤ {n} = n , +-zero n

suc-≤-suc : m ≤ n → suc m ≤ suc n
suc-≤-suc (k , p) = k , (+-suc k _) ∙ (cong suc p)

pred-≤-pred : suc m ≤ suc n → m ≤ n
pred-≤-pred (k , p) = k , injSuc ((sym (+-suc k _)) ∙ p)

≤-refl : m ≤ m
≤-refl = 0 , refl

≤-suc : m ≤ n → m ≤ suc n
≤-suc (k , p) = suc k , cong suc p

≤-trans : k ≤ m → m ≤ n → k ≤ n
≤-trans {k} {m} {n} (i , p) (j , q) = i + j , l2 ∙ (l1 ∙ q)
  where
  l1 : j + i + k ≡ j + m
  l1 = (sym (+-assoc j i k)) ∙ (cong (j +_) p)
  l2 : i + j + k ≡ j + i + k
  l2 = cong (_+ k) (+-comm i j)

≤-antisym : m ≤ n → n ≤ m → m ≡ n
≤-antisym {m} (i , p) (j , q) = (cong (_+ m) l3) ∙ p
  where
  l1 : j + i + m ≡ m
  l1 = (sym (+-assoc j i m)) ∙ ((cong (j +_) p) ∙ q)
  l2 : j + i ≡ 0
  l2 = m+n≡n→m≡0 l1
  l3 : 0 ≡ i
  l3 = sym (proj₂ (m+n≡0→m≡0×n≡0 l2))

¬-<-zero : ¬ m < 0
¬-<-zero (k , p) = snotz ((sym (+-suc k _)) ∙ p)

Trichotomy-suc : Trichotomy m n → Trichotomy (suc m) (suc n)
Trichotomy-suc (lt m<n) = lt (suc-≤-suc m<n)
Trichotomy-suc (eq m=n) = eq (cong suc m=n)
Trichotomy-suc (gt n<m) = gt (suc-≤-suc n<m)

_≟_ : ∀ m n → Trichotomy m n
zero ≟ zero = eq refl
zero ≟ suc n = lt (n , +-comm n 1)
suc m ≟ zero = gt (m , +-comm m 1)
suc m ≟ suc n = Trichotomy-suc (m ≟ n)
