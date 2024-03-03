{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Data.Fin.Inductive.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

open import Cubical.Relation.Nullary

-- inductive definition of <
_<ᵗ_ : (n m : ℕ) → Type
n <ᵗ zero = ⊥
zero <ᵗ suc m = Unit
suc n <ᵗ suc m = n <ᵗ m

data Trichotomyᵗ (m n : ℕ) : Type₀ where
  lt : m <ᵗ n → Trichotomyᵗ m n
  eq : m ≡ n → Trichotomyᵗ m n
  gt : n <ᵗ m → Trichotomyᵗ m n

Trichotomyᵗ-suc : {n m : ℕ} → Trichotomyᵗ n m → Trichotomyᵗ (suc n) (suc m)
Trichotomyᵗ-suc (lt x) = lt x
Trichotomyᵗ-suc (eq x) = eq (cong suc x)
Trichotomyᵗ-suc (gt x) = gt x

_≟ᵗ_ : ∀ m n → Trichotomyᵗ m n
zero ≟ᵗ zero = eq refl
zero ≟ᵗ suc n = lt tt
suc m ≟ᵗ zero = gt tt
suc m ≟ᵗ suc n = Trichotomyᵗ-suc (m ≟ᵗ n)

isProp<ᵗ : {n m : ℕ} → isProp (n <ᵗ m)
isProp<ᵗ {n = n} {zero} = isProp⊥
isProp<ᵗ {n = zero} {suc m} = isPropUnit
isProp<ᵗ {n = suc n} {suc m} = isProp<ᵗ {n = n} {m = m}
-- Fin defined using <ᵗ
Fin : (n : ℕ) → Type
Fin n = Σ[ m ∈ ℕ ] (m <ᵗ n)

fsuc : {n : ℕ} → Fin n → Fin (suc n)
fst (fsuc {n = n} (x , p)) = suc x
snd (fsuc {n = suc n} (x , p)) = p

<ᵗsucm : {m : ℕ} → m <ᵗ suc m
<ᵗsucm {m = zero} = tt
<ᵗsucm {m = suc m} = <ᵗsucm {m = m}

<ᵗ-trans-suc : {n m : ℕ} → n <ᵗ m → n <ᵗ suc m
<ᵗ-trans-suc {n = zero} {suc m} x = tt
<ᵗ-trans-suc {n = suc n} {suc m} x = <ᵗ-trans-suc  {n = n} x

¬-suc-n<ᵗn : {n : ℕ} → ¬ (suc n) <ᵗ n
¬-suc-n<ᵗn {suc n} = ¬-suc-n<ᵗn {n}

injectSuc : {n : ℕ} → Fin n → Fin (suc n)
fst (injectSuc {n = n} (x , p)) = x
snd (injectSuc {n = suc n} (x , p)) = <ᵗ-trans-suc {n = x} p

flast : {m : ℕ} → Fin (suc m)
fst (flast {m = m}) = m
snd (flast {m = m}) = <ᵗsucm {m = m}


-- Sums
sumFinGen : ∀ {ℓ} {A : Type ℓ} {n : ℕ} (_+_ : A → A → A) (0A : A) (f : Fin n → A) → A
sumFinGen {n = zero} _+_ 0A f = 0A
sumFinGen {n = suc n} _+_ 0A f = f flast + sumFinGen _+_ 0A (f ∘ injectSuc)
