{-# OPTIONS --safe #-}

module Cubical.Data.Nat.Primes.DecProps where

open import Cubical.Data.Nat.Primes.Imports
open import Cubical.Data.Nat.Primes.Lemmas
open import Cubical.Data.Nat.Primes.Base
open import Cubical.Data.Nat.Primes.Factors
open import Cubical.Data.Empty as ⊥ hiding (elim)
open import Cubical.Data.Sum.Properties
open import Cubical.Reflection.RecordEquiv

open isPrime
open isComposite


private
    variable
        ℓ ℓ' : Level

    funcProp : {A : Type ℓ} {B : A → Type ℓ'} → (∀ a → isProp (B a)) → isProp (∀ a → B a)
    funcProp BProp f g = funExt (λ x → BProp x (f x) (g x))

    PropIso : ∀ {A : Type ℓ} {B : Type ℓ'} → isProp A → isProp B → (A → B) → (B → A) → Iso A B
    PropIso propA propB fun inv = iso fun inv (λ _ → propB _ _) (λ _ → propA _ _)


primeProp : ∀ n → isProp (isPrime n)
primeProp n np np' i .n-proper = isProp≤ (np .n-proper) (np' .n-proper) i
primeProp n np np' i .primality =
    (funcProp  (λ x → funcProp  (λ x∣n →
    isProp⊎ (isSetℕ x 1) (isSetℕ x n)
    λ x=1 x=n → ¬n<n (subst (λ y → y < n) (sym x=1 ∙ x=n) (np .n-proper))))
    (np .primality) (np' .primality)) i

compProp : ∀ n → isProp (isComposite n)
compProp n nc nc' = answer where
    p1 = nc .p
    p2 = nc' .p
    q1 = nc .q
    q2 = nc' .q
    pp1 = nc .p-prime
    pp2 = nc' .p-prime
    1<p1 = pp1 .n-proper
    1<p2 = pp2 .n-proper
    1<q1 = nc .q-proper
    1<q2 = nc' .q-proper
    pq=n = nc .factors
    pq=n' = nc' .factors
    least1 = nc .least
    least2 = nc' .least

    p1∣n = ∣ (q1 , ·-comm q1 p1 ∙ pq=n) ∣₁
    p2∣n = ∣ (q2 , ·-comm q2 p2 ∙ pq=n') ∣₁

    p1=p2 : p1 ≡ p2
    p1=p2 = ≤-antisym (least1 p2 1<p2 p2∣n) (least2 p1 1<p1 p1∣n)

    q1=q2 : q1 ≡ q2
    q1=q2 = inj-·0< q1 q2 (<-weaken 1<p1) (pq=n ∙ sym (subst (λ x → x · q2 ≡ n) (sym p1=p2) pq=n'))

    leastProp : ∀ x → isProp ((p2' : ℕ) → 1 < p2' → p2' ∣ n → x ≤ p2')
    leastProp x = funcProp (λ a → funcProp (λ 1<a → funcProp (λ a∣n → isProp≤)))

    answer : nc ≡ nc'
    answer i .p = ≤-antisym (least1 p2 1<p2 p2∣n) (least2 p1 1<p1 p1∣n) i
    answer i .q = q1=q2 i
    answer i .p-prime = isProp→PathP (λ j → primeProp (p1=p2 j)) pp1 pp2 i
    answer i .q-proper = isProp→PathP (λ j → isProp≤ {n = q1=q2 j}) 1<q1 1<q2 i
    answer i .factors = isProp→PathP (λ j → isSetℕ (p1=p2 j · q1=q2 j) n) pq=n pq=n' i
    answer i .least = isProp→PathP (λ j → leastProp (p1=p2 j)) least1 least2 i


prime→¬comp : ∀ n → isPrime n → ¬ isComposite n
prime→¬comp n pn cn with (pn .primality) (cn .q) (∣ (cn .p , cn .factors) ∣₁)
... | inl q=1 = <≠ (cn .q-proper) (sym q=1)
... | inr q=n = <≠ (PropFac< qfac pfac n (n-proper pp) (<-weaken (pn .n-proper)) (·-comm qfac pfac ∙ pq=n)) q=n where
        pfac = cn .p
        pp = cn .p-prime
        qfac = cn .q
        pq=n = cn .factors

¬comp→prime : ∀ n → 1 < n → ¬ isComposite n → isPrime n
¬comp→prime n 1<n ¬nc with primeOrComp n 1<n
... | inl np = np
... | inr nc = ⊥.rec (¬nc nc)

comp→¬prime : ∀ n → isComposite n → ¬ isPrime n
comp→¬prime n nc np = prime→¬comp n np nc

¬prime→comp : ∀ n → 1 < n → ¬ isPrime n → isComposite n
¬prime→comp n 1<n ¬np with primeOrComp n 1<n
... | inr nc = nc
... | inl np = ⊥.rec (¬np np)

prime≡¬comp : ∀ n → 1 < n → (isPrime n) ≡ (¬ isComposite n)
prime≡¬comp n 1<n =
    isoToPath (PropIso (primeProp n) (isProp¬ (isComposite n)) (prime→¬comp n) (¬comp→prime n 1<n))

comp≡¬prime : ∀ n → 1 < n → (isComposite n) ≡ (¬ isPrime n)
comp≡¬prime n 1<n =
    isoToPath (PropIso (compProp n) (isProp¬ (isPrime n)) (comp→¬prime n) (¬prime→comp n 1<n))

DecPrime : ∀ n → Dec (isPrime n)
DecPrime 0 = no λ 0p → ¬-<-zero (0p .n-proper)
DecPrime 1 = no λ 1p → ¬n<n (1p .n-proper)
DecPrime n@(suc (suc n-2)) with (primeOrComp n (n-2 , +-comm n-2 2))
... | inl np = yes np
... | inr nc = no (comp→¬prime n nc)

DecComp : ∀ n → Dec (isComposite n)
DecComp 0 = no λ 0c → ¬n<n (<-trans (2 , refl) (isComposite.3<n 0c))
DecComp 1 = no λ 1c → ¬n<n (<-trans (1 , refl) (isComposite.3<n 1c))
DecComp n@(suc (suc n-2)) with (primeOrComp n (n-2 , +-comm n-2 2))
... | inr nc = yes nc
... | inl np = no (prime→¬comp n np)
