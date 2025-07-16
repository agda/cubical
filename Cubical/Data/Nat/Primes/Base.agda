{-# OPTIONS --safe #-}

module Cubical.Data.Nat.Primes.Base where

open import Cubical.Foundations.Prelude public
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Sum hiding (elim ; rec ; map)
open import Cubical.Data.Nat.Primes.Lemmas using (1<·1<=3<)


record isPrime (n : ℕ) : Type where
    -- no-eta-equality
    constructor prime
    field
        n-proper : 1 < n
        primality : ∀ d → d ∣ n → (d ≡ 1) ⊎ (d ≡ n)

record isComposite (n : ℕ) : Type where
    -- no-eta-equality
    constructor composite
    field
        p q : ℕ
        p-prime  : isPrime p
        q-proper : 1 < q
        factors : p · q ≡ n
        least : ∀ z → 1 < z → z ∣ n → p ≤ z

    3<n : 3 < n
    3<n = subst (λ x → 3 < x) factors (1<·1<=3< (isPrime.n-proper p-prime) q-proper)
