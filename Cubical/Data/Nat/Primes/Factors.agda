{-# OPTIONS --safe #-}

module Cubical.Data.Nat.Primes.Factors where

open import Cubical.Data.Nat.Primes.Imports
open import Cubical.Data.Nat.Primes.Lemmas
open import Cubical.Data.Nat.Primes.Base
open import Cubical.Data.Empty as ⊥ hiding (elim)


leastFactorIsPrime : ∀ n p → HasFactor n p → (∀ d → HasFactor n d → p ≤ d) → isPrime p
leastFactorIsPrime _ 0 (1<p , _) _ = ⊥.rec (¬-<-zero 1<p)
leastFactorIsPrime n p@(suc p-1) (1<p , p∣n) least = prime 1<p primality where
    primality : ∀ (d : ℕ) → d ∣ p → (d ≡ 1) ⊎ (d ≡ p)
    primality zero d∣p = ⊥.rec (¬z∣sn p-1 d∣p)
    primality d@(suc d-1) d∣p with ≤-split (m∣n→m≤n snotz d∣p)
    ... | inr d=p = inr d=p
    ... | inl d<p with (d ≟ 1)
    ... | eq d=1 = inl d=1
    ... | lt d<1 = ⊥.rec (¬s<1 d<1)
    ... | gt 1<d = ⊥.rec (<-asym d<p (least d (1<d , ∣-trans d∣p p∣n)))


primeOrComp : ∀ n → 1 < n → (isPrime n) ⊎ (isComposite n)
primeOrComp zero 1<0 = ⊥.rec (¬-<-zero 1<0)
primeOrComp n@(suc n-1) 1<n = answer where

    LF : Σ[ p ∈ ℕ ] (HasFactor n p) × (∀ z → (HasFactor n z) → p ≤ z)
    LF = findLeast (1<n , ∣-refl refl) DecHF

    p = LF .fst
    HFnp = LF .snd .fst
    1<p = HFnp .fst
    p∣n = ∣-untrunc (HFnp .snd)
    q = p∣n .fst
    p≤n = m∣n→m≤n snotz (HFnp .snd)
    pq=n = ·-comm p q ∙ p∣n .snd

    p-least : ∀ z → (HasFactor n z) → p ≤ z
    p-least = LF .snd .snd

    p-prime : isPrime p
    p-prime = leastFactorIsPrime n p HFnp p-least

    answer : (isPrime n) ⊎ (isComposite n)
    answer with (Dichotomyℕ n p)
    ... | inl n≤p = inl (subst (λ x → isPrime x) (≤-antisym p≤n n≤p) p-prime)
    ... | inr p<n = inr (composite p q p-prime 1<q pq=n (λ z 1<z z∣n → p-least z (1<z , z∣n)))
            where
                1<q : 1 < q
                1<q with (1 ≟ q)
                ... | lt 1<q = 1<q
                ... | gt q<1 = ⊥.rec (1<→¬=0 n 1<n
                                     (sym pq=n ∙ cong (p ·_) (<1→0 q q<1) ∙ sym (0≡m·0 p)))
                ... | eq 1=q = ⊥.rec (¬n<n (subst (λ x → x < n)
                                                  (subst
                                                        (λ x → p ≡ p · x)
                                                        1=q
                                                        (sym (·-identityʳ p)) ∙ pq=n)
                                                  p<n))

newPrime : ∀ n → Σ[ p ∈ ℕ ] (n < p) × (isPrime p)
newPrime n with primeOrComp (suc (factorial n)) (suc< (0<factorial n))
... | inl sfnp = (suc (factorial n)) , suc-≤-suc (n≤! n) , sfnp
... | inr (composite p q pp 1<q pq=n least) with Dichotomyℕ p n
... | inr n<p = p , n<p , pp
... | inl p≤n = ⊥.rec (<≠ 1<p (sym (div1→1 p p∣1))) where
        1<p = pp .isPrime.n-proper
        p∣1 : p ∣ 1
        p∣1 = ∣+-cancel p 1 (n !) (≤n∣n! p n p≤n (1<→¬=0 p 1<p)) (∥_∥₁.∣ q , ·-comm q p ∙ pq=n ∣₁)


record PrimeFactors (n : ℕ) : Type where
    no-eta-equality
    constructor pfs
    field
        primes : List ℕ
        factored : product primes ≡ n
        allPrime : All isPrime primes
open PrimeFactors

PF-prime : ∀ n → isPrime n → PrimeFactors n
PF-prime n np = pfs (n ∷ []) (·-identityʳ n) (np ∷ [])

PF-comp-work : ∀ n → (∀ m → m < n → isComposite m → PrimeFactors m) → isComposite n →
               PrimeFactors n
PF-comp-work n rec nComp@(composite p q p-prime 1<q pq=n _) =
    pfs (p ∷ primes qFacs)
        (subst (λ x → p · x ≡ n) (sym (factored qFacs)) pq=n)
        (p-prime ∷ allPrime qFacs)
        where
            qFacs : PrimeFactors q
            qFacs with (primeOrComp q 1<q)
            ... | inl qp = PF-prime q qp
            ... | inr qc = rec q (PropFac< q p n 1<p 0<n (·-comm q p ∙ pq=n)) qc where
                    1<p = isPrime.n-proper p-prime
                    0<n = <-trans (2 , refl) (isComposite.3<n nComp)

PF-comp : ∀ n → isComposite n → PrimeFactors n
PF-comp = WFI.induction <-wellfounded PF-comp-work

PF-aux : ∀ n → (isPrime n) ⊎ (isComposite n) → PrimeFactors n
PF-aux n (inl np) = PF-prime n np
PF-aux n (inr nc) = PF-comp n nc

factorize : ∀ n → 0 < n  → PrimeFactors n
factorize 0 0<0 = ⊥.rec (¬n<n 0<0)
factorize 1 _ = pfs [] refl []
factorize n@(suc (suc n-2)) _ = PF-aux n (primeOrComp n (n-2 , +-comm n-2 2))
