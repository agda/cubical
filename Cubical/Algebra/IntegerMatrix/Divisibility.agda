{-

Base facts about that the ring ℤ is Bézout domain

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.IntegerMatrix.Divisibility where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  hiding   (+-assoc ; +-comm ; ·-comm)
  renaming (_·_ to _·ℕ_; _+_ to _+ℕ_ ; ·-assoc to ·ℕ-assoc)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Mod
open import Cubical.Data.Int

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Relation.Nullary

private
  variable
    m n k : ℤ

-- The Divisibility Relation
-- Most definitions are the same as in Cubical.Data.Nat.Divisibility

_∣_ : ℤ → ℤ → Type₀
m ∣ n = ∃[ c ∈ ℤ ] c · m ≡ n

isProp∣ : isProp (m ∣ n)
isProp∣ = squash

∣-left : m ∣ (m · k)
∣-left {k = k} = ∣ k , ·Comm k _ ∣

∣-right : m ∣ (k · m)
∣-right {k = k} =  ∣ k , refl ∣

∣-refl : m ≡ n → m ∣ n
∣-refl p = ∣ 1 , p ∣

∣-zeroʳ : m ∣ 0
∣-zeroʳ = ∣ 0 , refl ∣

∣-+ : k ∣ m → k ∣ n → k ∣ (m + n)
∣-+ =
  Prop.map2
    λ {(c₁ , p) (c₂ , q) → (c₁ + c₂ , ·DistL+ c₁ c₂ _ ∙ (λ t → p t + q t))}

∣-trans : k ∣ m → m ∣ n → k ∣ n
∣-trans =
  Prop.map2
    λ {(c₁ , p) (c₂ , q) → (c₂ · c₁ , sym (·Assoc c₂ c₁ _) ∙ cong (c₂ ·_) p ∙ q)}

∣-right· : k ∣ m → k ∣ (n · m)
∣-right· {k = k} {n = n} p = ∣-trans p (∣-right {k = n})

-- Bézout and Euclidean Domain

record Bézout (m n : ℤ) : Type₀ where
  constructor bezout
  field
    coef₁ : ℤ
    coef₂ : ℤ
    gcd   : ℤ
    identity : coef₁ · m + coef₂ · n ≡ gcd
    isGCD : (gcd ∣ m) × (gcd ∣ n)

open Bézout

Bézout0 : (n : ℤ) → Bézout 0 n
Bézout0 n .coef₁ = 0
Bézout0 n .coef₂ = 1
Bézout0 n .gcd   = n
Bézout0 n .identity = +Comm 0 n
Bézout0 n .isGCD = ∣-zeroʳ , ∣-refl refl

perm-helper : (x y z w : ℤ) → (x + y) + (z + w) ≡ (x + z) + (w + y)
perm-helper x y z w =
    +Assoc (x + y) z w
  ∙ (λ t → +Assoc x y z (~ t) + w)
  ∙ sym (+Assoc x (y + z) w)
  ∙ (λ t → x + (+Comm y z t + w))
  ∙ (λ t → x + +Assoc z y w (~ t))
  ∙ +Assoc x z (y + w)
  ∙ (λ t → (x + z) + (+Comm y w t))

cancel-helper : (x y z : ℤ) → (- x · y) · z + x · (y · z) ≡ 0
cancel-helper x y z =
    (λ t → ·Assoc (- x) y z (~ t) + x · (y · z))
  ∙ (λ t → -DistL· x (y · z) (~ t) + x · (y · z))
  ∙ -Cancel' (x · (y · z))

alg-helper : (a b m d r : ℤ) → (- a · d + b) · m + a · (d · m + r) ≡ a · r + b · m
alg-helper a b m d r =
    (λ t → ·DistL+ (- a · d) b m t + ·DistR+ a (d · m) r t)
  ∙ perm-helper ((- a · d) · m) (b · m) (a · (d · m)) (a · r)
  ∙ (λ t → cancel-helper a d m t + (a · r + b · m))
  ∙ +Comm 0 _

bézoutReduction : (m d r : ℤ) → Bézout r m → Bézout m (d · m + r)
bézoutReduction m d r b .coef₁ = - b .coef₁ · d + b .coef₂
bézoutReduction m d r b .coef₂ = b .coef₁
bézoutReduction m d r b .gcd   = b .gcd
bézoutReduction m d r b .identity = alg-helper (b .coef₁) (b .coef₂) m d r ∙ b .identity
bézoutReduction m d r b .isGCD .fst = b .isGCD .snd
bézoutReduction m d r b .isGCD .snd = ∣-+ (∣-right· {n = d} (b .isGCD .snd)) (b .isGCD .fst)

-- Quotient and Remainder

record QuotRem (m n : ℤ) : Type₀ where
  constructor quotrem
  field
    div : ℤ
    rem : ℤ
    quotEq : n ≡ div · m + rem
    normIneq : (rem ≡ 0) ⊎ ((¬ rem ≡ 0) × (abs rem < abs m))

open QuotRem

-- The Euclidean Algorithm
module _
  (decEq0  : (n : ℤ) → Dec (n ≡ 0))
  (quotRem : (m n : ℤ)(¬z : ¬ m ≡ 0) → QuotRem m n) where

  euclidStep : (norm : ℕ)
    → (m n : ℤ)(h : abs m < norm)
    → (b : QuotRem m n)
    → Bézout m n
  euclidStep 0 _ _ h _ = Empty.rec (¬-<-zero h)
  euclidStep (suc N) m n h (quotrem div rem quotEq (inl p)) =
    let q = subst (λ r → n ≡ div · m + r) p quotEq
    in  bezout 1 0 m refl (∣-refl refl , subst (λ k → m ∣ k) (sym q) (∣-right {k = div}))
  euclidStep (suc N) m n h (quotrem div rem quotEq (inr p)) =
    let b = euclidStep N rem m (<≤-trans (p .snd) (pred-≤-pred h)) (quotRem _ _ (p .fst))
    in  subst (λ x → Bézout m x) (sym quotEq) (bézoutReduction _ div _ b)

  euclid-helper : (m n : ℤ)(dec : Dec (m ≡ 0)) → Bézout m n
  euclid-helper m n (yes z) = subst (λ x → Bézout x n) (sym z) (Bézout0 n)
  euclid-helper m n (no ¬z) = euclidStep (suc (abs m)) m n ≤-refl (quotRem m n ¬z)

  euclid : (m n : ℤ) → Bézout m n
  euclid m n = euclid-helper m n (decEq0 _)

-- The Ring ℤ is Euclidean Domain

dec-helper : {ℓ ℓ' : Level}{A : Type ℓ}{B : Type ℓ'} → Dec A → B → A ⊎ ((¬ A) × B)
dec-helper (yes p) _ = inl p
dec-helper (no ¬p) b = inr (¬p , b)

quotRemPosPos : (m n : ℕ)(¬z : ¬ pos m ≡ 0) → QuotRem (pos m) (pos n)
quotRemPosPos m n _ .div = pos (quotient  n / m)
quotRemPosPos m n _ .rem = pos (remainder n / m)
quotRemPosPos m n _ .quotEq =
    (λ t → pos (≡remainder+quotient m n (~ t)))
  ∙ pos+ (remainder n / m) (m ·ℕ (quotient n / m))
  ∙ +Comm (pos (remainder n / m)) (pos (m ·ℕ (quotient n / m)))
  ∙ (λ t → pos· m (quotient n / m) t + pos (remainder n / m))
  ∙ (λ t → ·Comm (pos m) (pos (quotient n / m)) t + pos (remainder n / m))
quotRemPosPos 0       n ¬z .normIneq = Empty.rec (¬z refl)
quotRemPosPos (suc m) n ¬z .normIneq = dec-helper (discreteℤ _ 0) (mod< m n)

quotRemNegPos : (m n : ℕ)(¬z : ¬ - pos m ≡ 0) → QuotRem (- pos m) (pos n)
quotRemNegPos m n ¬z .div = - (quotRemPosPos m n (λ p → ¬z (λ t → - p t)) .div)
quotRemNegPos m n ¬z .rem = quotRemPosPos m n (λ p → ¬z (λ t → - p t)) .rem
quotRemNegPos m n ¬z .quotEq =
    quotRemPosPos m n (λ p → ¬z (λ t → - p t)) .quotEq
  ∙ (λ t → -DistLR· (pos (quotient n / m)) (pos m) t + (pos (remainder n / m)))
quotRemNegPos 0       n ¬z .normIneq = Empty.rec (¬z refl)
quotRemNegPos (suc m) n ¬z .normIneq = quotRemPosPos (suc m) n (λ p → ¬z (λ t → - p t)) .normIneq

quotRemPos-helper : (m : ℤ)(k n : ℕ)(¬z : ¬ m ≡ 0) → (m ≡ pos k) ⊎ (m ≡ - pos k) → QuotRem m (pos n)
quotRemPos-helper m k n ¬z (inl p) =
  subst (λ l → QuotRem l (pos n)) (sym p) (quotRemPosPos k n (λ r → ¬z (p ∙ r)))
quotRemPos-helper m k n ¬z (inr p) =
  subst (λ l → QuotRem l (pos n)) (sym p) (quotRemNegPos k n (λ r → ¬z (p ∙ r)))

quotRemPos : (m : ℤ)(n : ℕ)(¬z : ¬ m ≡ 0) → QuotRem m (pos n)
quotRemPos m n ¬z = quotRemPos-helper m (abs m) n ¬z (abs→⊎ _ _ refl)

sum-helper : (m r : ℤ)
  → (r ≡ 0)   ⊎ ((¬ r ≡ 0)   × (abs r < abs m))
  → (- r ≡ 0) ⊎ ((¬ - r ≡ 0) × (abs (- r) < abs m))
sum-helper m r (inl p) = inl (λ t → - p t)
sum-helper m r (inr p) =
  inr ((λ q → p .fst (sym (-Involutive r) ∙ (λ t → - q t)))
    , subst (λ k → k < abs m) (sym (abs- r)) (p .snd))

quotRemNeg : (m : ℤ)(n : ℕ)(¬z : ¬ m ≡ 0) → QuotRem m (- pos n)
quotRemNeg m n ¬z .div = - (quotRemPos m n ¬z .div)
quotRemNeg m n ¬z .rem = - (quotRemPos m n ¬z .rem)
quotRemNeg m n ¬z .quotEq =
    (λ t → - quotRemPos m n ¬z .quotEq t)
  ∙ -Dist+ (quotRemPos m n ¬z .div · m) (quotRemPos m n ¬z .rem)
  ∙ (λ t → -DistL· (quotRemPos m n ¬z .div) m t + - quotRemPos m n ¬z .rem)
quotRemNeg m n ¬z .normIneq = sum-helper m _ (quotRemPos m n ¬z .normIneq)

quotRem-helper : (m n : ℤ)(k : ℕ)(¬z : ¬ m ≡ 0) → (n ≡ pos k) ⊎ (n ≡ - pos k) → QuotRem m n
quotRem-helper m n k ¬z (inl p) = subst (λ l → QuotRem m l) (sym p) (quotRemPos m k ¬z)
quotRem-helper m n k ¬z (inr p) = subst (λ l → QuotRem m l) (sym p) (quotRemNeg m k ¬z)

quotRem : (m n : ℤ)(¬z : ¬ m ≡ 0) → QuotRem m n
quotRem m n ¬z = quotRem-helper m n (abs n) ¬z (abs→⊎ _ _ refl)

bézout : (m n : ℤ) → Bézout m n
bézout = euclid (λ m → discreteℤ m 0) quotRem
