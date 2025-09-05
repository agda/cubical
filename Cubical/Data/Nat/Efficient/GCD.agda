module Cubical.Data.Nat.Efficient.GCD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Mod renaming (
  quotient'_/_  to _/_ ; remainder'_/_ to _%_
  ; ≡remainder'+quotient' to ≡%+·/ ; mod'< to %< )
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Nat.GCD hiding (
  stepGCD ; euclid< ; euclid ; isContrGCD ; gcd ;
  gcdIsGCD ; isGCD→gcd≡ ; gcd≡→isGCD ; gcd-factorʳ ; isGCD-multʳ
  ) public

private
  variable
    m n d : ℕ

-- a pair of useful lemmas about ∣ and (efficient) %
  ∣→∣% : ∀ {m n d} → d ∣ m → d ∣ n → d ∣ (m % n)
  ∣%→∣ : ∀ {m n d} → d ∣ (m % n) → d ∣ n → d ∣ m

∣→∣% {m} {0}         {d} d∣m d∣n = d∣m
∣→∣% {m} {n@(suc _)} {d} d∣m d∣n =
  let
    k₁     = ∣-untrunc d∣m .fst
    k₁·d≡m = ∣-untrunc d∣m .snd
    k₂     = ∣-untrunc d∣n .fst
    k₂·d≡n = ∣-untrunc d∣n .snd
    p      =
      (k₁ ∸ m / n · k₂) · d         ≡⟨ ∸-distribʳ k₁ (m / n · k₂) d ⟩
      k₁ · d ∸ m / n · k₂ · d       ≡⟨ sym $ cong (k₁ · d ∸_) (·-assoc (m / n) _ _) ⟩
      k₁ · d ∸ m / n · (k₂ · d)     ≡⟨ cong₂ (λ l r → l ∸ m / n · r) k₁·d≡m k₂·d≡n ⟩
      m ∸ m / n · n                 ≡⟨ cong (m ∸_) (·-comm (m / n) n) ⟩
      m ∸ n · m / n                 ≡⟨ sym $ cong (_∸ n · m / n) (≡%+·/ n m)  ⟩
      m % n + n · m / n ∸ n · m / n ≡⟨ +∸ (m % n) (n · m / n) ⟩
      m % n                         ∎
  in
    ∣ k₁ ∸ m / n · k₂ , p ∣₁

∣%→∣ {m} {0}         {d} d∣m%n d∣n = d∣m%n
∣%→∣ {m} {n@(suc _)} {d} d∣m%n d∣n =
  let
    k₁       = ∣-untrunc d∣m%n .fst
    k₁·d≡m%n = ∣-untrunc d∣m%n .snd
    k₂       = ∣-untrunc d∣n   .fst
    k₂·d≡n   = ∣-untrunc d∣n   .snd
    p        =
      (k₁ + k₂ · m / n) · d     ≡⟨ sym $ ·-distribʳ k₁ (k₂ · m / n) d ⟩
      k₁ · d + k₂ · m / n · d   ≡⟨ cong (λ p → k₁ · d + p · d) (·-comm k₂ (m / n)) ⟩
      k₁ · d + m / n · k₂ · d   ≡⟨ sym $ cong (k₁ · d +_) (·-assoc (m / n) k₂ d) ⟩
      k₁ · d + m / n · (k₂ · d) ≡⟨ cong₂ (λ l r → l + m / n · r) k₁·d≡m%n k₂·d≡n ⟩
      m % n + m / n · n         ≡⟨ cong (m % n +_) (·-comm (m / n) n) ⟩
      m % n + n · m / n         ≡⟨ ≡%+·/ n m ⟩
      m                         ∎
  in
    ∣ k₁ + k₂ · m / n , p ∣₁

-- The inductive step of the Euclidean algorithm
stepGCD : isGCD (suc n) (m % suc n) d
        → isGCD m       (suc n)     d
stepGCD w =
  let
    g∣1+n            = w .fst .fst
    g∣m%1+n          = w .fst .snd
    d∣1+n→d∣m%1+n→d∣g = w .snd
  in
    (∣%→∣ g∣m%1+n g∣1+n , g∣1+n) ,
    λ d' (d'∣m , d'∣1+n) → d∣1+n→d∣m%1+n→d∣g d' (d'∣1+n , (∣→∣% d'∣m d'∣1+n))

-- putting it all together using an auxiliary variable to pass the termination checking

euclid-helper< : (m n f : ℕ) → (n < m) → (m ≤ f) → GCD m n
euclid-helper< m       n       zero    n<m m≤0 .fst = 0
euclid-helper< m       n       zero    n<m m≤0 .snd .fst .fst = ∣-refl $ sym $ ≤0→≡0 m≤0
euclid-helper< m       n       zero    n<m m≤0 .snd .fst .snd = ∣-refl $ sym $ ≤0→≡0 $
                                                             <-weaken $ <≤-trans n<m m≤0
euclid-helper< m       n       zero    n<m m≤0 .snd .snd d' _ = ∣-zeroʳ d'
euclid-helper< zero    zero    (suc _) _   _   .fst = 0
euclid-helper< zero    zero    (suc _) _   _   .snd .fst .fst = ∣-refl refl
euclid-helper< zero    zero    (suc _) _   _   .snd .fst .snd = ∣-refl refl
euclid-helper< zero    zero    (suc _) _   _   .snd .snd d' _ = ∣-zeroʳ d'
euclid-helper< zero    (suc n) (suc _) _   _   .fst = suc n
euclid-helper< zero    (suc n) (suc _) _   _   .snd .fst .fst = ∣-zeroʳ (suc n)
euclid-helper< zero    (suc n) (suc _) _   _   .snd .fst .snd = ∣-refl refl
euclid-helper< zero    (suc n) (suc _) _   _   .snd .snd d' (_ , d'∣1+n) = d'∣1+n
euclid-helper< (suc m) zero    (suc _) _   _   .fst = suc m
euclid-helper< (suc m) zero    (suc _) _   _   .snd .fst .fst = ∣-refl refl
euclid-helper< (suc m) zero    (suc _) _   _   .snd .fst .snd = ∣-zeroʳ (suc m)
euclid-helper< (suc m) zero    (suc _) _   _   .snd .snd d' (d'∣1+m , _) = d'∣1+m
euclid-helper< m@(suc _) n@(suc n-1) (suc f) n<m m≤1+f =
  let
    n≤f = predℕ-≤-predℕ $ <≤-trans n<m m≤1+f
    r   = euclid-helper< n (m % n) f (%< n-1 m) n≤f
  in
    r .fst , stepGCD (r .snd)

euclid : ∀ m n → GCD m n
euclid m zero        = m , (∣-refl refl , ∣-zeroʳ m) , λ d' (d'∣m , _) → d'∣m
euclid m n@(suc n-1) =
  let
    r = euclid-helper< n (m % n) n (%< n-1 m) ≤-refl
  in
    r .fst , stepGCD (r .snd)

isContrGCD : ∀ m n → isContr (GCD m n)
isContrGCD m n = euclid m n , isPropGCD _

-- the gcd operator on ℕ

gcd : ℕ → ℕ → ℕ
gcd m n = euclid m n .fst

gcdIsGCD : ∀ m n → isGCD m n (gcd m n)
gcdIsGCD m n = euclid m n .snd

isGCD→gcd≡ : isGCD m n d → gcd m n ≡ d
isGCD→gcd≡ dGCD = cong fst (isContrGCD _ _ .snd (_ , dGCD))

gcd≡→isGCD : gcd m n ≡ d → isGCD m n d
gcd≡→isGCD p = subst (isGCD _ _) p (gcdIsGCD _ _)


-- multiplicative properties of the gcd

gcd-factorʳ : ∀ m n k → gcd (m · k) (n · k) ≡ gcd m n · k
gcd-factorʳ m n zero = (λ i → gcd (0≡m·0 m (~ i)) (0≡m·0 n (~ i))) ∙ 0≡m·0 (gcd m n)
gcd-factorʳ m n (suc k) = sym p ∙ cong (_· suc k) (sym q)
  where k∣gcd : suc k ∣ gcd (m · suc k) (n · suc k)
        k∣gcd = gcdIsGCD (m · suc k) (n · suc k) .snd (suc k) (∣-right m , ∣-right n)
        d' = ∣-untrunc k∣gcd .fst
        p : d' · suc k ≡ gcd (m · suc k) (n · suc k)
        p = ∣-untrunc k∣gcd .snd

        d'GCD : isGCD m n d'
        d'GCD = isGCD-cancelʳ _ (subst (isGCD _ _) (sym p) (gcdIsGCD (m · suc k) (n · suc k)))
        q : gcd m n ≡ d'
        q = isGCD→gcd≡ d'GCD

-- Q: Can this be proved directly? (i.e. without a transport)
isGCD-multʳ : ∀ k → isGCD m n d
                  → isGCD (m · k) (n · k) (d · k)
isGCD-multʳ {m} {n} {d} k dGCD = gcd≡→isGCD (gcd-factorʳ m n k ∙ cong (_· k) r)
  where r : gcd m n ≡ d
        r = isGCD→gcd≡ dGCD
