{-# OPTIONS --safe #-}

module Cubical.Data.Nat.Primes.DecProps where

open import Cubical.Data.Nat.Primes.Imports
open import Cubical.Data.Nat.Primes.Lemmas
open import Cubical.Data.Nat.Primes.Base
open import Cubical.Data.Nat.Primes.Factors
open import Cubical.Data.Empty as ⊥ hiding (elim)
open import Cubical.Data.Sum.Properties

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
primeProp n (prime 1<n primality) (prime 1<n' primality') =
    cong₂ prime
    (isProp≤ 1<n 1<n')
    (funcProp  (λ x → funcProp  (λ x∣n →
    isProp⊎ (isSetℕ x 1) (isSetℕ x n)
    λ x=1 x=n → ¬n<n (subst (λ y → y < n) (sym x=1 ∙ x=n) 1<n)
    ))
    primality primality' )

compProp : ∀ n → isProp (isComposite n)
compProp n (composite p q pp 1<q pq=n least) (composite p' q' pp' 1<q' pq=n' least') =
    λ i → composite
    (p=p' i)
    (q=q' i)
    ((isProp→PathP (λ j → primeProp (p=p' j)) pp pp') i)
    ((isProp→PathP (λ j → isProp≤ {n = q=q' j}) 1<q 1<q') i)
    ((isProp→PathP (λ j → isSetℕ (p=p' j · q=q' j) n) pq=n pq=n') i)
    ((isProp→PathP (λ j → leastProp (p=p' j)) least least') i)
    where
        1<p : 1 < p
        1<p = n-proper pp
        1<p' : 1 < p'
        1<p' = n-proper pp'

        p∣n : p ∣ n
        p∣n = ∣ (q , ·-comm q p ∙ pq=n) ∣₁
        p'∣n : p' ∣ n
        p'∣n = ∣ (q' , ·-comm q' p' ∙ pq=n') ∣₁

        p=p' : p ≡ p'
        p=p' = ≤-antisym (least p' 1<p' p'∣n) (least' p 1<p p∣n)

        q=q' : q ≡ q'
        q=q' = inj-·0< q q' (<-weaken 1<p) (pq=n ∙ sym (subst (λ x → x · q' ≡ n) (sym p=p') pq=n'))

        leastProp : ∀ x → isProp ((p'' : ℕ) → 1 < p'' → p'' ∣ n → x ≤ p'')
        leastProp x = funcProp (λ a → funcProp (λ 1<a → funcProp (λ a∣n → isProp≤)))

prime→¬comp : ∀ n → isPrime n → ¬ isComposite n
prime→¬comp n (prime 1<n primality) (composite p q pp 1<q pq=n _)
    with (primality q ∣ (p , pq=n) ∣₁)
... | inl q=1 = <≠ 1<q (sym q=1)
... | inr q=n = <≠ (PropFac< q p n (n-proper pp) (<-weaken 1<n) (·-comm q p ∙ pq=n)) q=n

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
DecPrime 0 = no λ (prime 1<0 _) → ¬-<-zero 1<0
DecPrime 1 = no λ (prime 1<1 _) → ¬n<n 1<1
DecPrime n@(suc (suc n-2)) with (primeOrComp n (n-2 , +-comm n-2 2))
... | inl np = yes np
... | inr nc = no (comp→¬prime n nc)

DecComp : ∀ n → Dec (isComposite n)
DecComp 0 = no λ 0c → ¬n<n (<-trans (2 , refl) (isComposite.3<n 0c))
DecComp 1 = no λ 1c → ¬n<n (<-trans (1 , refl) (isComposite.3<n 1c))
DecComp n@(suc (suc n-2)) with (primeOrComp n (n-2 , +-comm n-2 2))
... | inr nc = yes nc
... | inl np = no (prime→¬comp n np)
