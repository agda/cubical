{-# OPTIONS --safe #-}

module Cubical.Data.Nat.Primes.Infinitude where

open import Cubical.Data.Nat.Primes.Imports
open import Cubical.Data.Nat.Primes.Lemmas
open import Cubical.Data.Nat.Primes.Base
open import Cubical.Data.Nat.Primes.Split
open import Cubical.Data.Nat.Primes.Concrete
open import Cubical.Data.Nat.Primes.Factors
open import Cubical.Data.Nat.Primes.DecProps


nextPrime : (n : ℕ) → Σ[ p ∈ ℕ ] ((n < p) × (isPrime p)) × ((z : ℕ) → (n < z) × isPrime z → p ≤ z)
nextPrime n = findLeast (((newPrime n) .snd)) (DecProd (<Dec n) DecPrime)

nthPrime : (n : ℕ) → Σ[ p ∈ ℕ ] isPrime p × (countBelow isPrime DecPrime p ≡ n)
nthPrime zero = (least-prime .fst , least-prime .snd .fst , refl) where
    least-prime = findLeast prime2 DecPrime
nthPrime (suc n) = (next-prime .fst , next-prime .snd .fst .snd , snprimes) where
    IH = nthPrime n

    p#n = IH .fst
    p#n-prime = IH .snd .fst
    #p<p#n=n = IH .snd .snd

    next-prime : Σ[ q ∈ ℕ ] ((p#n < q) × isPrime q) × (∀ z → (p#n < z) × isPrime z → q ≤ z)
    next-prime = nextPrime p#n

    q = next-prime .fst
    p#n<q = next-prime .snd .fst .fst
    p#n≤q = <-weaken p#n<q
    q-prime = next-prime .snd .fst .snd
    q-least = next-prime .snd .snd

    sum : countBelow isPrime DecPrime q
          ≡ countRange isPrime DecPrime p#n q p#n≤q + countBelow isPrime DecPrime p#n
    sum = sym (countWorks isPrime DecPrime p#n q p#n≤q)
    p1 : countRange isPrime DecPrime p#n q p#n≤q ≡ 1
    p1 = leastAboveLow isPrime DecPrime p#n q p#n-prime
         (isPropDec (primeProp p#n) (DecPrime p#n) (yes p#n-prime))
         q-least p#n<q

    snprimes : countBelow isPrime DecPrime q ≡ suc n
    snprimes = sum ∙ add-equations p1 #p<p#n=n


open Iso
ℕ≅primeℕ : Iso ℕ (Σ ℕ isPrime)
fun      ℕ≅primeℕ n = (pn .fst , pn .snd .fst) where pn = nthPrime n
inv      ℕ≅primeℕ (p , _) = countBelow isPrime DecPrime p
leftInv  ℕ≅primeℕ n = nthPrime n .snd .snd
rightInv ℕ≅primeℕ (p , p-prime) =
    ΣPathP (answer , isProp→PathP (λ i → primeProp (answer i)) pn-prime p-prime) where
        pn = nthPrime (countBelow isPrime DecPrime p)
        pn-prime = pn .snd .fst
        answer : pn .fst ≡ p
        answer = countBelowYesInj isPrime DecPrime (pn .fst) p pn-prime p-prime
                 (isPropDec (primeProp (pn .fst)) (DecPrime (pn .fst)) (yes pn-prime))
                 (isPropDec (primeProp p) (DecPrime p) (yes p-prime))
                 (pn .snd .snd)
