module Cubical.Data.Nat.Order.Inductive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Data.Bool.Base hiding (_≟_)

open import Cubical.Induction.WellFounded

open import Cubical.Relation.Nullary

-- TODO: unify with recursive.agda

-- alternative definition of <
_<ᵗ_ : (n m : ℕ) → Type
n <ᵗ m = Bool→Type (n <ᵇ m)

_≤ᵗ_ : (n m : ℕ) → Type
n ≤ᵗ m = n <ᵗ suc m

_>ᵗ_ : (n m : ℕ) → Type
n >ᵗ m = m <ᵗ n

_≥ᵗ_ : (n m : ℕ) → Type
n ≥ᵗ m = m ≤ᵗ n

-- <ᵗ satisfies the following judgemental equalities,
-- which give <ᵗ an "inductive" presentation, justifying the module name:
private
  _ : ∀ {n} → n <ᵗ zero ≡ ⊥
  _ = refl

  _ : ∀ {m} → zero <ᵗ suc m ≡ Unit
  _ = refl

  _ : ∀ {n m} → suc n <ᵗ suc m ≡ n <ᵗ m
  _ = refl

  -- direct inductive definition (avoided for performance reasons):
  -- _<ᵗ_ : (n m : ℕ) → Type
  -- n <ᵗ zero = ⊥
  -- zero <ᵗ suc m = Unit
  -- suc n <ᵗ suc m = n <ᵗ m

data Trichotomyᵗ (m n : ℕ) : Type₀ where
  lt : m <ᵗ n → Trichotomyᵗ m n
  eq : m ≡ n → Trichotomyᵗ m n
  gt : n <ᵗ m → Trichotomyᵗ m n

Trichotomyᵗ-suc : {n m : ℕ} → Trichotomyᵗ n m
  → Trichotomyᵗ (suc n) (suc m)
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
isProp<ᵗ {n = zero} {suc m} _ _ = refl
isProp<ᵗ {n = suc n} {suc m} = isProp<ᵗ {n = n} {m = m}

<ᵗsucm : {m : ℕ} → m <ᵗ suc m
<ᵗsucm {m = zero} = tt
<ᵗsucm {m = suc m} = <ᵗsucm {m = m}

<ᵗ-trans-suc : {n m : ℕ} → n <ᵗ m → n <ᵗ suc m
<ᵗ-trans-suc {n = zero} {suc m} x = tt
<ᵗ-trans-suc {n = suc n} {suc m} x = <ᵗ-trans-suc  {n = n} x

¬-suc-n<ᵗn : {n : ℕ} → ¬ (suc n) <ᵗ n
¬-suc-n<ᵗn {suc n} = ¬-suc-n<ᵗn {n}

<ᵗ-trans : {n m k : ℕ} → n <ᵗ m → m <ᵗ k → n <ᵗ k
<ᵗ-trans {n = zero} {suc m} {suc k} _ _ = tt
<ᵗ-trans {n = suc n} {suc m} {suc k} = <ᵗ-trans {n = n} {m} {k}

¬m<ᵗm : {m : ℕ} → ¬ (m <ᵗ m)
¬m<ᵗm {m = suc m} p = ¬m<ᵗm {m = m} p

<ᵗ-+ : {n k : ℕ} → n <ᵗ suc (k + n)
<ᵗ-+ {n = zero} {k} = tt
<ᵗ-+ {n = suc n} {k} =
  subst (n <ᵗ_) (sym (+-suc k n)) (<ᵗ-+ {n = n} {k})

¬squeeze : {n m : ℕ} → ¬ ((n <ᵗ m) × (m <ᵗ suc n))
¬squeeze {n = suc n} {suc m} = ¬squeeze {n = n} {m = m}

<ᵗ→< : {n m : ℕ} → n <ᵗ m → n < m
<ᵗ→< {n = zero} {suc m} p = m , +-comm m 1
<ᵗ→< {n = suc n} {suc m} p = suc-≤-suc (<ᵗ→< {n = n} {m = m} p)

<→<ᵗ : {n m : ℕ} → n < m → n <ᵗ m
<→<ᵗ {n = zero} {m = zero} x =
  snotz (sym (+-suc (fst x) 0) ∙ snd x)
<→<ᵗ {n = zero} {m = suc m} _ = tt
<→<ᵗ {n = suc n} {m = zero} x =
  snotz (sym (+-suc (fst x) (suc n)) ∙ snd x)
<→<ᵗ {n = suc n} {m = suc m} p = <→<ᵗ {n = n} {m = m} (pred-≤-pred p)

<ᵗ-asym : ∀ {m n} → m <ᵗ n → n ≤ m → ⊥
<ᵗ-asym p = <-asym (<ᵗ→< p)

private
  acc-suc : ∀ {n} → Acc _<ᵗ_ n → Acc _<ᵗ_ (suc n)
  acc-suc {n} (acc ih) = acc λ where
      zero    _  → acc (λ m p → ⊥.rec p)
      (suc m) p  → acc-suc (ih m p)

<ᵗ-wellfounded : WellFounded _<ᵗ_
<ᵗ-wellfounded zero = acc λ _ → ⊥.rec
<ᵗ-wellfounded (suc n) = acc-suc ((<ᵗ-wellfounded n))

module _ {n m : ℕ} where
  isPropTrichotomyᵗ : isProp (Trichotomyᵗ n m)
  isPropTrichotomyᵗ (lt x) (lt y) i = lt (isProp<ᵗ {n = n} {m} x y i)
  isPropTrichotomyᵗ (lt x) (eq y) = ⊥.rec (¬m<ᵗm {m} (subst (_<ᵗ m) y x))
  isPropTrichotomyᵗ (lt x) (gt y) = ⊥.rec (¬m<ᵗm {m} (<ᵗ-trans {m} {n} {m} y x))
  isPropTrichotomyᵗ (eq x) (lt y) =
    ⊥.rec (¬m<ᵗm {m} (subst (_<ᵗ m) x y))
  isPropTrichotomyᵗ (eq x) (eq y) i = eq (isSetℕ n m x y i)
  isPropTrichotomyᵗ (eq x) (gt y) = ⊥.rec (¬m<ᵗm {n} (subst (_<ᵗ n) (sym x) y))
  isPropTrichotomyᵗ (gt x) (lt y) = ⊥.rec (¬m<ᵗm {n} (<ᵗ-trans {n} {m} {n} y x))
  isPropTrichotomyᵗ (gt x) (eq y) = ⊥.rec (¬m<ᵗm {n} (subst (_<ᵗ n) (sym y) x))
  isPropTrichotomyᵗ (gt x) (gt y) i = gt (isProp<ᵗ {n = m} {n} x y i)

module falseDichotomies where
  lt-eq : {n m : ℕ} → ¬ m <ᵗ n × (m ≡ suc n)
  lt-eq {n = n} (p , q) = ¬-suc-n<ᵗn {n = n} (subst (_<ᵗ n) q p)

  lt-gt : {n m : ℕ}  → ¬ m <ᵗ n × (suc n <ᵗ m)
  lt-gt {n = n} {m} (p , q) =
    ¬-suc-n<ᵗn {n = n} (<ᵗ-trans {n = suc n} {m} {n} q p)

  eq-eq : {n m : ℕ} → ¬ (m ≡ n) × (m ≡ suc n)
  eq-eq {n = n} (p , q) =
    ¬m<ᵗm {n} (subst (_<ᵗ suc n) (sym p ∙ q) (<ᵗsucm {n}))

  eq-gt : {n m : ℕ} → ¬ (m ≡ n) × (suc n <ᵗ m)
  eq-gt (p , q) = lt-eq (q , cong suc (sym p))

  gt-lt : {n m : ℕ} → ¬ (n <ᵗ m) × (m <ᵗ suc n)
  gt-lt {n = n} {m = m} = ¬squeeze {n = n} {m = m}
