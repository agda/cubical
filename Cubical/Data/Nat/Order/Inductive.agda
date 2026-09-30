module Cubical.Data.Nat.Order.Inductive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Data.Bool hiding (_≤_)

open import Cubical.Induction.WellFounded

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    R : Type ℓ
    P : ℕ → Type ℓ
    k l m n : ℕ

-- alternative definition of <

infix 4 _<ᵗ_ _≤ᵗ_ _>ᵗ_ _≥ᵗ_

_<ᵗ_ : (n m : ℕ) → Type
n <ᵗ m = Bool→Type (n <ᵇ m)

_≤ᵗ_ : (n m : ℕ) → Type
n ≤ᵗ m = n <ᵗ suc m

_>ᵗ_ : (n m : ℕ) → Type
n >ᵗ m = m <ᵗ n

_≥ᵗ_ : (n m : ℕ) → Type
n ≥ᵗ m = m ≤ᵗ n

-- <ᵗ satisfies the following judgmental equalities,
-- which give <ᵗ an "inductive" presentation, justifying the module name:
private
  _ : ∀ {n} → (n <ᵗ zero) ≡ ⊥
  _ = refl

  _ : ∀ {m} → (zero <ᵗ suc m) ≡ Unit
  _ = refl

  _ : ∀ {n m} → (suc n <ᵗ suc m) ≡ (n <ᵗ m)
  _ = refl

  -- direct inductive definition (avoided for performance reasons):
  -- _<ᵗ_ : (n m : ℕ) → Type
  -- n <ᵗ zero = ⊥
  -- zero <ᵗ suc m = Unit
  -- suc n <ᵗ suc m = n <ᵗ m

_<ᵗ?_ : (m n : ℕ) → Dec (m <ᵗ n)
m <ᵗ? n = m <ᵇ? n

_≤ᵗ?_ : (m n : ℕ) → Dec (m ≤ᵗ n)
m ≤ᵗ? n = m <ᵇ? (suc n)

data Trichotomyᵗ (m n : ℕ) : Type₀ where
  lt : m <ᵗ n → Trichotomyᵗ m n
  eq : m ≡ n → Trichotomyᵗ m n
  gt : n <ᵗ m → Trichotomyᵗ m n

Trichotomyᵗ-suc : {n m : ℕ} → Trichotomyᵗ n m
  → Trichotomyᵗ (suc n) (suc m)
Trichotomyᵗ-suc (lt x) = lt x
Trichotomyᵗ-suc (eq x) = eq (cong suc x)
Trichotomyᵗ-suc (gt x) = gt x

-- NOTE:
-- This function computes very slowly for concrete numbers.
-- However, it has a useful definitional identity that has been used in several modules:
--  (suc m) ≟ᵗ (suc n) = Trichotomyᵗ-suc (m ≟ᵗ n)
-- therefore, we keep it here as the default implementation.
-- For a more efficient implementation, see `_≟ᶠ_` below

_≟ᵗ_ : ∀ m n → Trichotomyᵗ m n
zero ≟ᵗ zero = eq refl
zero ≟ᵗ suc n = lt tt
suc m ≟ᵗ zero = gt tt
suc m ≟ᵗ suc n = Trichotomyᵗ-suc (m ≟ᵗ n)

isProp<ᵗ : isProp (n <ᵗ m)
isProp<ᵗ = isPropBool→Type

isProp≤ᵗ : isProp (n ≤ᵗ m)
isProp≤ᵗ = isPropBool→Type

≤ᵗ-+ˡ : m ≤ᵗ n → k + m ≤ᵗ k + n
≤ᵗ-+ˡ {k = zero}  m≤n = m≤n
≤ᵗ-+ˡ {k = suc k} m≤n = ≤ᵗ-+ˡ {k = k} m≤n

≤ᵗ-+ʳ : m ≤ᵗ n → m + k ≤ᵗ n + k
≤ᵗ-+ʳ {m} {n} {k} m≤n
  = transport (λ i → +-comm k m i ≤ᵗ +-comm k n i) (≤ᵗ-+ˡ {m} {n} {k} m≤n)

≤ᵗ-refl : ∀ m → m ≤ᵗ m
≤ᵗ-refl zero = _
≤ᵗ-refl (suc m) = ≤ᵗ-refl m

≤ᵗ-trans : k ≤ᵗ m → m ≤ᵗ n → k ≤ᵗ n
≤ᵗ-trans {zero} _ _ = _
≤ᵗ-trans {suc k} {suc m} {suc n} = ≤ᵗ-trans {k} {m} {n}

≤ᵗ-antisym : m ≤ᵗ n → n ≤ᵗ m → m ≡ n
≤ᵗ-antisym {zero} {zero} _ _ = refl
≤ᵗ-antisym {suc m} {suc n} m≤n n≤m = cong suc (≤ᵗ-antisym m≤n n≤m)

≤ᵗ-+-cancelˡ : k + m ≤ᵗ k + n → m ≤ᵗ n
≤ᵗ-+-cancelˡ {k =  zero} m≤n = m≤n
≤ᵗ-+-cancelˡ {k = suc k} m≤n = ≤ᵗ-+-cancelˡ {k} m≤n

≤ᵗ-+-cancelʳ : m + k ≤ᵗ n + k → m ≤ᵗ n
≤ᵗ-+-cancelʳ {m} {k} {n}
  = ≤ᵗ-+-cancelˡ {k} {m} {n} ∘ transport λ i → +-comm m k i ≤ᵗ +-comm n k i

≤ᵗ0→≡0 : n ≤ᵗ 0 → n ≡ 0
≤ᵗ0→≡0 {zero} _ = refl

≤ᵗSumLeft : ∀ k → k ≤ᵗ k + n
≤ᵗSumLeft zero    = _
≤ᵗSumLeft (suc k) = ≤ᵗSumLeft k

≤ᵗSumRight : ∀ n → n ≤ᵗ k + n
≤ᵗSumRight {k} n = transport (λ i → n ≤ᵗ +-comm n k i) (≤ᵗSumLeft n)

¬<ᵗ→≥ᵗ : {m n : ℕ} → ¬ m <ᵗ n → n ≤ᵗ m
¬<ᵗ→≥ᵗ {m} {n} = ¬<ᵇ→≥ᵇ m n

¬≤ᵗ→>ᵗ : {m n : ℕ} → ¬ m ≤ᵗ n → n <ᵗ m
¬≤ᵗ→>ᵗ {m} {n} = ¬≤ᵇ→>ᵇ m n

<ᵗsuc : {m : ℕ} → m <ᵗ suc m
<ᵗsuc {m = zero} = tt
<ᵗsuc {m = suc m} = <ᵗsuc {m = m}

<ᵗ-trans-suc : {n m : ℕ} → n <ᵗ m → n <ᵗ suc m
<ᵗ-trans-suc {n = zero} {suc m} x = tt
<ᵗ-trans-suc {n = suc n} {suc m} x = <ᵗ-trans-suc  {n = n} x

¬-sucℕ-<ᵗ : {n : ℕ} → ¬ (suc n) <ᵗ n
¬-sucℕ-<ᵗ {suc n} = ¬-sucℕ-<ᵗ {n}

<ᵗ-trans : {n m k : ℕ} → n <ᵗ m → m <ᵗ k → n <ᵗ k
<ᵗ-trans {n = zero} {suc m} {suc k} _ _ = tt
<ᵗ-trans {n = suc n} {suc m} {suc k} = <ᵗ-trans {n = n} {m} {k}

<ᵗ-irrefl : {m : ℕ} → ¬ (m <ᵗ m)
<ᵗ-irrefl {m = suc m} p = <ᵗ-irrefl {m = m} p

¬SumLeft<ᵗ : {m n : ℕ} → ¬ m + n <ᵗ m
¬SumLeft<ᵗ {suc m} = ¬SumLeft<ᵗ {m}

<ᵗ-weaken : {m n : ℕ} → m <ᵗ n → m ≤ᵗ n
<ᵗ-weaken {zero} _ = _
<ᵗ-weaken {suc m} {suc n} = <ᵗ-weaken {m}

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

<ᵗ-asym' : {m n : ℕ} → m <ᵗ n → ¬ n <ᵗ m
<ᵗ-asym' {m} m<n n<m = <ᵗ-irrefl {m} (<ᵗ-trans {m} {_} {m} m<n n<m)

<ᵗ→≢ : {n m : ℕ} → n <ᵗ m → ¬ n ≡ m
<ᵗ→≢ {n} {m} p q = <ᵗ-irrefl {m = m} (subst {x = n} (_<ᵗ m) q p)

_≟ᶠ_ : ∀ m n → Trichotomyᵗ m n
m ≟ᶠ n with m <ᵗ? n
... | yes m<n = lt m<n
... | no ¬m<n with n <ᵗ? m
... | yes n<m = gt n<m
... | no ¬n<m = eq (≤ᵗ-antisym (¬<ᵇ→≥ᵇ n m ¬n<m) (¬<ᵇ→≥ᵇ m n ¬m<n))

≤ᵗ-split : {m n : ℕ} → m ≤ᵗ n → (m <ᵗ n) ⊎ (m ≡ n)
≤ᵗ-split {m} {n} m≤n with m <ᵗ? n
... | yes m<n = inl m<n
... | no ¬m<n = inr (≤ᵗ-antisym m≤n (¬<ᵇ→≥ᵇ m n ¬m<n))

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
  isPropTrichotomyᵗ (lt x) (eq y) = ⊥.rec (<ᵗ-irrefl {m} (subst (_<ᵗ m) y x))
  isPropTrichotomyᵗ (lt x) (gt y) = ⊥.rec (<ᵗ-irrefl {m} (<ᵗ-trans {m} {n} {m} y x))
  isPropTrichotomyᵗ (eq x) (lt y) = ⊥.rec (<ᵗ-irrefl {m} (subst (_<ᵗ m) x y))
  isPropTrichotomyᵗ (eq x) (eq y) i = eq (isSetℕ n m x y i)
  isPropTrichotomyᵗ (eq x) (gt y) = ⊥.rec (<ᵗ-irrefl {n} (subst (_<ᵗ n) (sym x) y))
  isPropTrichotomyᵗ (gt x) (lt y) = ⊥.rec (<ᵗ-irrefl {n} (<ᵗ-trans {n} {m} {n} y x))
  isPropTrichotomyᵗ (gt x) (eq y) = ⊥.rec (<ᵗ-irrefl {n} (subst (_<ᵗ n) (sym y) x))
  isPropTrichotomyᵗ (gt x) (gt y) i = gt (isProp<ᵗ {n = m} {n} x y i)

module falseDichotomies where
  lt-eq : {n m : ℕ} → ¬ (m <ᵗ n) × (m ≡ suc n)
  lt-eq {n = n} (p , q) = ¬-sucℕ-<ᵗ {n = n} (subst (_<ᵗ n) q p)

  lt-gt : {n m : ℕ}  → ¬ (m <ᵗ n) × (suc n <ᵗ m)
  lt-gt {n = n} {m} (p , q) =
    ¬-sucℕ-<ᵗ {n = n} (<ᵗ-trans {n = suc n} {m} {n} q p)

  eq-eq : {n m : ℕ} → ¬ (m ≡ n) × (m ≡ suc n)
  eq-eq {n = n} (p , q) =
    <ᵗ-irrefl {n} (subst (_<ᵗ suc n) (sym p ∙ q) (<ᵗsuc {n}))

  eq-gt : {n m : ℕ} → ¬ (m ≡ n) × (suc n <ᵗ m)
  eq-gt (p , q) = lt-eq (q , cong suc (sym p))

  gt-lt : {n m : ℕ} → ¬ (n <ᵗ m) × (m <ᵗ suc n)
  gt-lt {n = n} {m = m} = ¬squeeze {n = n} {m = m}

module WellFounded where
  wf-<ᵗ : WellFounded _<ᵗ_
  wf-rec-<ᵗ : ∀ n → WFRec _<ᵗ_ (Acc _<ᵗ_) n

  wf-<ᵗ n = acc (wf-rec-<ᵗ n)

  wf-rec-<ᵗ (suc n) m m≤n with ≤ᵗ-split {m} {n} m≤n
  ... | inl m<n = wf-rec-<ᵗ n m m<n
  ... | inr m≡n = subst⁻ (Acc _<ᵗ_) m≡n (wf-<ᵗ n)

wf-elim : (∀ n → (∀ m → m <ᵗ n → P m) → P n) → ∀ n → P n
wf-elim = WFI.induction WellFounded.wf-<ᵗ

wf-rec : (∀ n → (∀ m → m <ᵗ n → R) → R) → ℕ → R
wf-rec {R = R} = wf-elim {P = λ _ → R}

module Minimal where
  Least : ∀{ℓ} → (ℕ → Type ℓ) → (ℕ → Type ℓ)
  Least P m = P m × (∀ n → n <ᵗ m → ¬ P n)

  isPropLeast : (∀ m → isProp (P m)) → ∀ m → isProp (Least P m)
  isPropLeast pP m
    = isPropΣ (pP m) (λ _ → isPropΠ3 λ _ _ _ → isProp⊥)

  Least→ : Σ _ (Least P) → Σ _ P
  Least→ = map-snd fst

  private
    search-lemma : ∀ n → ¬ P 0 → (∀ m → m <ᵗ n → ¬ P (suc m)) → ∀ m → m <ᵗ suc n → ¬ P m
    search-lemma n ¬P0 ¬P<1+n zero    = λ _ → ¬P0
    search-lemma n ¬P0 ¬P<1+n (suc m) = ¬P<1+n m

  search
    : (∀ m → Dec (P m))
    → ∀ n → (Σ[ m ∈ ℕ ] Least P m) ⊎ (∀ m → m <ᵗ n → ¬ P m)
  search {P = P} dec zero    = inr λ _ b _ → b
  search {P = P} dec (suc n) with dec 0
  ... | yes P0 = inl (0 , P0 , λ _ b _ → b)
  ... | no ¬P0 with search {P = P ∘ suc} (dec ∘ suc) n
  ... | inl (m , P1+m , ¬P<1+m) = inl (suc m , P1+m , search-lemma m ¬P0 ¬P<1+m)
  ... | inr ¬P<1+n              = inr (search-lemma n ¬P0 ¬P<1+n)

  →Least : (∀ m → Dec (P m)) → Σ _ P → Σ _ (Least P)
  →Least dec (n , Pn) with search dec n
  ... | inl least = least
  ... | inr ¬P<n  = n , Pn , ¬P<n

  Least-unique : ∀ m n → Least P m → Least P n → m ≡ n
  Least-unique m n (Pm , ¬P<m) (Pn , ¬P<n) with m ≟ᶠ n
  ... | lt m<n = ⊥.rec (¬P<n m m<n Pm)
  ... | eq m≡n = m≡n
  ... | gt n<m = ⊥.rec (¬P<m n n<m Pn)

  isPropΣLeast : (∀ m → isProp (P m)) → isProp (Σ _ (Least P))
  isPropΣLeast pP (m , LPm) (n , LPn)
    = ΣPathP λ where
        .fst → Least-unique m n LPm LPn
        .snd → isOfHLevel→isOfHLevelDep 1 (isPropLeast pP)
                LPm LPn (Least-unique m n LPm LPn)

  Decidable→Collapsible
    : (∀ m → isProp (P m)) → (∀ m → Dec (P m)) → Collapsible (Σ ℕ P)
  Decidable→Collapsible pP dP = λ where
    .fst → Least→ ∘ →Least dP
    .snd x y → cong Least→ (isPropΣLeast pP (→Least dP x) (→Least dP y))

open Minimal using (Decidable→Collapsible) public
