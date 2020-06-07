{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Nat.GCD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Induction.WellFounded

open import Cubical.Data.Fin
open import Cubical.Data.Sigma as Σ
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility

private
  variable
    m n d : ℕ

-- common divisors

isCD : ℕ → ℕ → ℕ → Type₀
isCD m n d = (d ∣ m) × (d ∣ n)

isPropIsCD : isProp (isCD m n d)
isPropIsCD = isProp× isProp∣ isProp∣

symCD : isCD m n d → isCD n m d
symCD (d∣m , d∣n) = (d∣n , d∣m)

-- greatest common divisors

isGCD : ℕ → ℕ → ℕ → Type₀
isGCD m n d = (isCD m n d) × (∀ d' → isCD m n d' → d' ∣ d)

GCD : ℕ → ℕ → Type₀
GCD m n = Σ ℕ (isGCD m n)

isPropIsGCD : isProp (isGCD m n d)
isPropIsGCD = isProp× isPropIsCD (isPropΠ2 (λ _ _ → isProp∣))

isPropGCD : isProp (GCD m n)
isPropGCD (d , dCD , gr) (d' , d'CD , gr') =
  Σ≡Prop (λ _ → isPropIsGCD) (antisym∣ (gr' d dCD) (gr d' d'CD))


symGCD : isGCD m n d → isGCD n m d
symGCD (dCD , gr) = symCD dCD , λ { d' d'CD → gr d' (symCD d'CD) }

divsGCD : m ∣ n → isGCD m n m
divsGCD p = (∣-refl refl , p) , λ { d (d∣m , _) → d∣m }


-- The base case of the Euclidean algorithm
zeroGCD : ∀ m → isGCD m 0 m
zeroGCD m = divsGCD (∣-zeroʳ m)

private
  lem₁ : prediv d (suc n) → prediv d (m % suc n) → prediv d m
  lem₁ {d} {n} {m} (c₁ , p₁) (c₂ , p₂) = (q * c₁ + c₂) , p
    where r = m % suc n; q = n%k≡n[modk] m (suc n) .fst
          p = (q * c₁ + c₂) * d     ≡⟨ sym (*-distribʳ (q * c₁) c₂ d) ⟩
              (q * c₁) * d + c₂ * d ≡⟨ cong (_+ c₂ * d) (sym (*-assoc q c₁ d))  ⟩
              q * (c₁ * d) + c₂ * d ≡[ i ]⟨ q * (p₁ i) + (p₂ i) ⟩
              q * (suc n)  + r      ≡⟨ n%k≡n[modk] m (suc n) .snd ⟩
              m                     ∎

  lem₂ : prediv d (suc n) → prediv d m → prediv d (m % suc n)
  lem₂ {d} {n} {m} (c₁ , p₁) (c₂ , p₂) = c₂ ∸ q * c₁ , p
    where r = m % suc n; q = n%k≡n[modk] m (suc n) .fst
          p = (c₂ ∸ q * c₁) * d               ≡⟨ ∸-distribʳ c₂ (q * c₁) d ⟩
              c₂ * d ∸ (q * c₁) * d           ≡⟨ cong (c₂ * d ∸_) (sym (*-assoc q c₁ d)) ⟩
              c₂ * d ∸ q * (c₁ * d)           ≡[ i ]⟨ p₂ i ∸ q * (p₁ i) ⟩
              m      ∸ q * (suc n)            ≡⟨ cong (_∸ q * (suc n)) (sym (n%k≡n[modk] m (suc n) .snd)) ⟩
              (q * (suc n) + r) ∸ q * (suc n) ≡⟨ cong (_∸ q * (suc n)) (+-comm (q * (suc n)) r) ⟩
              (r + q * (suc n)) ∸ q * (suc n) ≡⟨ ∸-cancelʳ r zero (q * (suc n)) ⟩
              r ∎

-- The inductive step of the Euclidean algorithm
stepGCD : isGCD (suc n) (m % suc n) d
        → isGCD m       (suc n)     d
fst (stepGCD ((d∣n , d∣m%n) , gr)) = PropTrunc.map2 lem₁ d∣n d∣m%n , d∣n
snd (stepGCD ((d∣n , d∣m%n) , gr)) d' (d'∣m , d'∣n) = gr d' (d'∣n , PropTrunc.map2 lem₂ d'∣n d'∣m)

-- putting it all together using well-founded induction

euclid< : ∀ m n → n < m → GCD m n
euclid< = WFI.induction <-wellfounded λ {
  m rec zero    p → m , zeroGCD m ;
  m rec (suc n) p → let d , dGCD = rec (suc n) p (m % suc n) (n%sk<sk m n)
                     in d , stepGCD dGCD }

euclid : ∀ m n → GCD m n
euclid m n with n ≟ m
... | lt p = euclid< m n p
... | gt p = Σ.map-snd symGCD (euclid< n m p)
... | eq p = m , divsGCD (∣-refl (sym p))

isContrGCD : ∀ m n → isContr (GCD m n)
isContrGCD m n = euclid m n , isPropGCD _

-- the gcd operator on ℕ

gcd : ℕ → ℕ → ℕ
gcd m n = euclid m n .fst

gcdIsGCD : ∀ m n → isGCD m n (gcd m n)
gcdIsGCD m n = euclid m n .snd
