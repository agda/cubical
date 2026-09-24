{-# OPTIONS --safe #-}

module Cubical.Data.Nat.Primes.Concrete where

open import Cubical.Data.Nat.Primes.Imports
open import Cubical.Data.Nat.Primes.Lemmas
open import Cubical.Data.Nat.Primes.Base
open import Cubical.Data.Empty as ⊥ hiding (elim)


prime2 : isPrime 2
prime2 = prime (0 , refl) primality-2 where
    primality-2 : (d : ℕ) → d ∣ 2 → (d ≡ 1) ⊎ (d ≡ 2)
    primality-2 d d∣2 with (≤-split (m∣n→m≤n snotz d∣2))
    ... | inr d=2 = inr d=2
    ... | inl d<2 with <-split d<2
    ... | inr d=1 = inl d=1
    ... | inl d<1 = ⊥.rec (¬<1∣sn d 1 d<1 d∣2)


private

    -- can be used to directly prove primality of a specific number
    notDiv : ∀ d n → Σ[ k ∈ ℕ ] (k · d < n) × (n < suc k · d) → ¬ d ∣ n
    notDiv d n (k , kd<n , n<d+kd) d∣n-trunc
        with d | (∣-untrunc d∣n-trunc) | (fst (∣-untrunc d∣n-trunc) ≟ k)
    ...       | d | (c , cd=n) | (eq c=k) = <≠ kd<n (subst (λ x → x · d ≡ n) c=k cd=n)
    ...       | 0 | (c , cd=n) | (lt c<k) = ¬-<-zero (subst (λ x → k · 0 < x)
                                                            (sym (cd=n) ∙ sym (0≡m·0 c))
                                                            kd<n)
    ... | suc d-1 | (c , cd=n) | (lt c<k) = <≠ (lem1 c k d-1 n c<k kd<n) cd=n
    ...       | d | (0 , cd=n) | (gt k<c) = ¬-<-zero k<c
    ... | d | (suc c , d+cd=n) | (gt k<sc) with (<-split k<sc)
    ...                        | inr k=c = <≠ n<d+kd
                                           (sym (subst (λ x → d + x · d ≡ n) (sym k=c) d+cd=n))
    ...                        | inl k<c = <≠ (lem2 c k d n k<c n<d+kd) (sym d+cd=n)

    -- example
    prime5 : isPrime 5
    prime5 = prime (3 , refl) primality-5 where
        primality-5 : (d : ℕ) → d ∣ 5 → (d ≡ 1) ⊎ (d ≡ 5)
        primality-5 d d∣5 with (≤-split (m∣n→m≤n snotz d∣5))
        ... | inr d=5 = inr d=5
        ... | inl d<5 with <-split d<5
        ... | inr d=4 = ⊥.rec (notDiv 4 5 (1 , (0 , refl) , (2 , refl)) (subst (λ x → x ∣ 5) d=4 d∣5))
        ... | inl d<4 with <-split d<4
        ... | inr d=3 = ⊥.rec (notDiv 3 5 (1 , (1 , refl) , (0 , refl)) (subst (λ x → x ∣ 5) d=3 d∣5))
        ... | inl d<3 with <-split d<3
        ... | inr d=2 = ⊥.rec (notDiv 2 5 (2 , (0 , refl) , (0 , refl)) (subst (λ x → x ∣ 5) d=2 d∣5))
        ... | inl d<2 with <-split d<2
        ... | inr d=1 = inl d=1
        ... | inl d<1 = ⊥.rec (¬<1∣sn d 4 d<1 d∣5)
