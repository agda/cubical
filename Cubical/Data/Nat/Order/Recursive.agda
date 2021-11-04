{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.Recursive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty
open import Cubical.Data.Unit

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties

open import Cubical.Relation.Nullary

infix 4 _≤_ _<_

_≤_ : ℕ → ℕ → Type₀
zero ≤ _ = Unit
suc m ≤ zero = ⊥
suc m ≤ suc n = m ≤ n

_<_ : ℕ → ℕ → Type₀
m < n = suc m ≤ n

_≤?_ : (m n : ℕ) → Dec (m ≤ n)
zero  ≤? _     = yes tt
suc m ≤? zero  = no λ ()
suc m ≤? suc n = m ≤? n

data Trichotomy (m n : ℕ) : Type₀ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

private
  variable
    k l m n : ℕ

m≤n-isProp : isProp (m ≤ n)
m≤n-isProp {zero} = isPropUnit
m≤n-isProp {suc m} {zero}  = isProp⊥
m≤n-isProp {suc m} {suc n} = m≤n-isProp {m} {n}

≤-k+ : m ≤ n → k + m ≤ k + n
≤-k+ {k = zero}  m≤n = m≤n
≤-k+ {k = suc k} m≤n = ≤-k+ {k = k} m≤n

≤-+k : m ≤ n → m + k ≤ n + k
≤-+k {m} {n} {k} m≤n
  = transport (λ i → +-comm k m i ≤ +-comm k n i) (≤-k+ {m} {n} {k} m≤n)

≤-refl : ∀ m → m ≤ m
≤-refl zero = _
≤-refl (suc m) = ≤-refl m

≤-trans : k ≤ m → m ≤ n → k ≤ n
≤-trans {zero} _ _ = _
≤-trans {suc k} {suc m} {suc n} = ≤-trans {k} {m} {n}

≤-antisym : m ≤ n → n ≤ m → m ≡ n
≤-antisym {zero} {zero} _ _ = refl
≤-antisym {suc m} {suc n} m≤n n≤m = cong suc (≤-antisym m≤n n≤m)

≤-k+-cancel : k + m ≤ k + n → m ≤ n
≤-k+-cancel {k =  zero} m≤n = m≤n
≤-k+-cancel {k = suc k} m≤n = ≤-k+-cancel {k} m≤n

≤-+k-cancel : m + k ≤ n + k → m ≤ n
≤-+k-cancel {m} {k} {n}
  = ≤-k+-cancel {k} {m} {n} ∘ transport λ i → +-comm m k i ≤ +-comm n k i

¬m<m : ¬ m < m
¬m<m {suc m} = ¬m<m {m}

≤0→≡0 : n ≤ 0 → n ≡ 0
≤0→≡0 {zero} _ = refl

¬m+n<m : ¬ m + n < m
¬m+n<m {suc m} = ¬m+n<m {m}

<-weaken : m < n → m ≤ n
<-weaken {zero} _ = _
<-weaken {suc m} {suc n} = <-weaken {m}

<→≢ : n < m → ¬ n ≡ m
<→≢ {n} {m} p q = ¬m<m {m = m} (subst {x = n} (_< m) q p)

Trichotomy-suc : Trichotomy m n → Trichotomy (suc m) (suc n)
Trichotomy-suc (lt m<n) = lt m<n
Trichotomy-suc (eq m≡n) = eq (cong suc m≡n)
Trichotomy-suc (gt n<m) = gt n<m

_≟_ : ∀ m n → Trichotomy m n
zero  ≟ zero = eq refl
zero  ≟ suc n = lt _
suc m ≟ zero = gt _
suc m ≟ suc n = Trichotomy-suc (m ≟ n)

k≤k+n : ∀ k → k ≤ k + n
k≤k+n zero    = _
k≤k+n (suc k) = k≤k+n k

n≤k+n : ∀ n → n ≤ k + n
n≤k+n {k} n = transport (λ i → n ≤ +-comm n k i) (k≤k+n n)
