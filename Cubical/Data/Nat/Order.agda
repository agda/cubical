{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Data.Nat.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels


open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties

open import Cubical.Induction.WellFounded

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level

infix 4 _≤_ _<_ _≥_ _>_

_≤_ : ℕ → ℕ → Type₀
m ≤ n = Σ[ k ∈ ℕ ] k + m ≡ n

_<_ : ℕ → ℕ → Type₀
m < n = suc m ≤ n

_≥_ : ℕ → ℕ → Type₀
m ≥ n = n ≤ m

_>_ : ℕ → ℕ → Type₀
m > n = n < m

data Trichotomy (m n : ℕ) : Type₀ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

private
  variable
    k l m n : ℕ

private
  witness-prop : ∀ j → isProp (j + m ≡ n)
  witness-prop {m} {n} j = isSetℕ (j + m) n

isProp≤ : isProp (m ≤ n)
isProp≤ {m} {n} (k , p) (l , q)
  = Σ≡Prop witness-prop lemma
  where
  lemma : k ≡ l
  lemma = inj-+m (p ∙ (sym q))

zero-≤ : 0 ≤ n
zero-≤ {n} = n , +-zero n

suc-≤-suc : m ≤ n → suc m ≤ suc n
suc-≤-suc (k , p) = k , (+-suc k _) ∙ (cong suc p)

≤-+k : m ≤ n → m + k ≤ n + k
≤-+k {m} {k = k} (i , p)
  = i , +-assoc i m k ∙ cong (_+ k) p

≤SumRight : n ≤ k + n
≤SumRight {n} {k} = ≤-+k zero-≤

≤-k+ : m ≤ n → k + m ≤ k + n
≤-k+ {m} {n} {k}
  = subst (_≤ k + n) (+-comm m k)
  ∘ subst (m + k ≤_) (+-comm n k)
  ∘ ≤-+k

≤SumLeft : n ≤ n + k
≤SumLeft {n} {k} = subst (n ≤_) (+-comm k n) (≤-+k zero-≤)

pred-≤-pred : suc m ≤ suc n → m ≤ n
pred-≤-pred (k , p) = k , injSuc ((sym (+-suc k _)) ∙ p)

≤-refl : m ≤ m
≤-refl = 0 , refl

≤-suc : m ≤ n → m ≤ suc n
≤-suc (k , p) = suc k , cong suc p

suc-< : suc m < n → m < n
suc-< p = pred-≤-pred (≤-suc p)

≤-sucℕ : n ≤ suc n
≤-sucℕ = ≤-suc ≤-refl

≤-predℕ : predℕ n ≤ n
≤-predℕ {zero} = ≤-refl
≤-predℕ {suc n} = ≤-suc ≤-refl

≤-trans : k ≤ m → m ≤ n → k ≤ n
≤-trans {k} {m} {n} (i , p) (j , q) = i + j , l2 ∙ (l1 ∙ q)
  where
  l1 : j + i + k ≡ j + m
  l1 = (sym (+-assoc j i k)) ∙ (cong (j +_) p)
  l2 : i + j + k ≡ j + i + k
  l2 = cong (_+ k) (+-comm i j)

≤-antisym : m ≤ n → n ≤ m → m ≡ n
≤-antisym {m} (i , p) (j , q) = (cong (_+ m) l3) ∙ p
  where
  l1 : j + i + m ≡ m
  l1 = (sym (+-assoc j i m)) ∙ ((cong (j +_) p) ∙ q)
  l2 : j + i ≡ 0
  l2 = m+n≡n→m≡0 l1
  l3 : 0 ≡ i
  l3 = sym (snd (m+n≡0→m≡0×n≡0 l2))

≤-+-≤ : m ≤ n → l ≤ k → m + l ≤ n + k
≤-+-≤ p q = ≤-trans (≤-+k p) (≤-k+ q)

≤-k+-cancel : k + m ≤ k + n → m ≤ n
≤-k+-cancel {k} {m} (l , p) = l , inj-m+ (sub k m ∙ p)
 where
 sub : ∀ k m → k + (l + m) ≡ l + (k + m)
 sub k m = +-assoc k l m ∙ cong (_+ m) (+-comm k l) ∙ sym (+-assoc l k m)

≤-+k-cancel : m + k ≤ n + k → m ≤ n
≤-+k-cancel {m} {k} {n} (l , p) = l , cancelled
 where
 cancelled : l + m ≡ n
 cancelled = inj-+m (sym (+-assoc l m k) ∙ p)

≤-+k-trans : (m + k ≤ n) → m ≤ n
≤-+k-trans {m} {k} {n} p = ≤-trans (k , +-comm k m) p

≤-k+-trans : (k + m ≤ n) → m ≤ n
≤-k+-trans {m} {k} {n} p = ≤-trans (m , refl) p

≤-·k : m ≤ n → m · k ≤ n · k
≤-·k {m} {n} {k} (d , r) = d · k , reason where
  reason : d · k + m · k ≡ n · k
  reason = d · k + m · k ≡⟨ ·-distribʳ d m k ⟩
           (d + m) · k   ≡⟨ cong (_· k) r ⟩
           n · k         ∎

<-k+-cancel : k + m < k + n → m < n
<-k+-cancel {k} {m} {n} = ≤-k+-cancel ∘ subst (_≤ k + n) (sym (+-suc k m))

¬-<-zero : ¬ m < 0
¬-<-zero (k , p) = snotz ((sym (+-suc k _)) ∙ p)

¬m<m : ¬ m < m
¬m<m {m} = ¬-<-zero ∘ ≤-+k-cancel {k = m}

≤0→≡0 : n ≤ 0 → n ≡ 0
≤0→≡0 {zero} ineq = refl
≤0→≡0 {suc n} ineq = ⊥.rec (¬-<-zero ineq)

predℕ-≤-predℕ : m ≤ n → (predℕ m) ≤ (predℕ n)
predℕ-≤-predℕ {zero} {zero}   ineq = ≤-refl
predℕ-≤-predℕ {zero} {suc n}  ineq = zero-≤
predℕ-≤-predℕ {suc m} {zero}  ineq = ⊥.rec (¬-<-zero ineq)
predℕ-≤-predℕ {suc m} {suc n} ineq = pred-≤-pred ineq

¬m+n<m : ¬ m + n < m
¬m+n<m {m} {n} = ¬-<-zero ∘ <-k+-cancel ∘ subst (m + n <_) (sym (+-zero m))

<-weaken : m < n → m ≤ n
<-weaken (k , p) = suc k , sym (+-suc k _) ∙ p

≤<-trans : l ≤ m → m < n → l < n
≤<-trans p = ≤-trans (suc-≤-suc p)

<≤-trans : l < m → m ≤ n → l < n
<≤-trans = ≤-trans

<-trans : l < m → m < n → l < n
<-trans p = ≤<-trans (<-weaken p)

<-asym : m < n → ¬ n ≤ m
<-asym m<n = ¬m<m ∘ <≤-trans m<n

<-+k : m < n → m + k < n + k
<-+k p = ≤-+k p

<-k+ : m < n → k + m < k + n
<-k+ {m} {n} {k} p = subst (λ km → km ≤ k + n) (+-suc k m) (≤-k+ p)

<-+k-trans : (m + k < n) → m < n
<-+k-trans {m} {k} {n} p = ≤<-trans (k , +-comm k m) p

<-k+-trans : (k + m < n) → m < n
<-k+-trans {m} {k} {n} p = ≤<-trans (m , refl) p

<-+-< : m < n → k < l → m + k < n + l
<-+-<  m<n k<l = <-trans (<-+k m<n) (<-k+ k<l)

<-+-≤ : m < n → k ≤ l → m + k < n + l
<-+-≤ p q = <≤-trans (<-+k p) (≤-k+ q)

<-·sk : m < n → m · suc k < n · suc k
<-·sk {m} {n} {k} (d , r) = (d · suc k + k) , reason where
  reason : (d · suc k + k) + suc (m · suc k) ≡ n · suc k
  reason = (d · suc k + k) + suc (m · suc k) ≡⟨ sym (+-assoc (d · suc k) k _) ⟩
           d · suc k + (k + suc (m · suc k)) ≡[ i ]⟨ d · suc k + +-suc k (m · suc k) i ⟩
           d · suc k + suc m · suc k         ≡⟨ ·-distribʳ d (suc m) (suc k) ⟩
           (d + suc m) · suc k               ≡⟨ cong (_· suc k) r ⟩
           n · suc k                         ∎

∸-≤ : ∀ m n → m ∸ n ≤ m
∸-≤ m zero = ≤-refl
∸-≤ zero (suc n) = ≤-refl
∸-≤ (suc m) (suc n) = ≤-trans (∸-≤ m n) (1 , refl)

≤-∸-+-cancel : m ≤ n → (n ∸ m) + m ≡ n
≤-∸-+-cancel {zero} {n} _ = +-zero _
≤-∸-+-cancel {suc m} {zero} m≤n = ⊥.rec (¬-<-zero m≤n)
≤-∸-+-cancel {suc m} {suc n} m+1≤n+1 = +-suc _ _ ∙ cong suc (≤-∸-+-cancel (pred-≤-pred m+1≤n+1))

≤-∸-suc : m ≤ n → suc (n ∸ m) ≡ suc n ∸ m
≤-∸-suc {zero} {n} m≤n = refl
≤-∸-suc {suc m} {zero} m≤n = ⊥.rec (¬-<-zero m≤n)
≤-∸-suc {suc m} {suc n} m+1≤n+1 = ≤-∸-suc (pred-≤-pred m+1≤n+1)

≤-∸-k : m ≤ n → k + (n ∸ m) ≡ (k + n) ∸ m
≤-∸-k {m} {n} {zero} r = refl
≤-∸-k {m} {n} {suc k} r = cong suc (≤-∸-k r) ∙ ≤-∸-suc (≤-trans r (k , refl))

left-≤-max : m ≤ max m n
left-≤-max {zero} {n} = zero-≤
left-≤-max {suc m} {zero} = ≤-refl
left-≤-max {suc m} {suc n} = suc-≤-suc left-≤-max

right-≤-max : n ≤ max m n
right-≤-max {zero} {m} = zero-≤
right-≤-max {suc n} {zero} = ≤-refl
right-≤-max {suc n} {suc m} = suc-≤-suc right-≤-max

min-≤-left : min m n ≤ m
min-≤-left {zero} {n} = ≤-refl
min-≤-left {suc m} {zero} = zero-≤
min-≤-left {suc m} {suc n} = suc-≤-suc min-≤-left

min-≤-right : min m n ≤ n
min-≤-right {zero} {n} = zero-≤
min-≤-right {suc m} {zero} = ≤-refl
min-≤-right {suc m} {suc n} = suc-≤-suc min-≤-right

≤Dec : ∀ m n → Dec (m ≤ n)
≤Dec zero n = yes (n , +-zero _)
≤Dec (suc m) zero = no ¬-<-zero
≤Dec (suc m) (suc n) with ≤Dec m n
... | yes m≤n = yes (suc-≤-suc m≤n)
... | no m≰n = no λ m+1≤n+1 → m≰n (pred-≤-pred m+1≤n+1 )

≤Stable : ∀ m n → Stable (m ≤ n)
≤Stable m n = Dec→Stable (≤Dec m n)

<Dec : ∀ m n → Dec (m < n)
<Dec m n = ≤Dec (suc m) n

<Stable : ∀ m n → Stable (m < n)
<Stable m n = Dec→Stable (<Dec m n)

Trichotomy-suc : Trichotomy m n → Trichotomy (suc m) (suc n)
Trichotomy-suc (lt m<n) = lt (suc-≤-suc m<n)
Trichotomy-suc (eq m=n) = eq (cong suc m=n)
Trichotomy-suc (gt n<m) = gt (suc-≤-suc n<m)

_≟_ : ∀ m n → Trichotomy m n
zero ≟ zero = eq refl
zero ≟ suc n = lt (n , +-comm n 1)
suc m ≟ zero = gt (m , +-comm m 1)
suc m ≟ suc n = Trichotomy-suc (m ≟ n)

Dichotomyℕ : ∀ (n m : ℕ) → (n ≤ m) ⊎ (n > m)
Dichotomyℕ n m with (n ≟ m)
... | lt x = inl (<-weaken x)
... | Trichotomy.eq x = inl (0 , x)
... | gt x = inr x

splitℕ-≤ : (m n : ℕ) → (m ≤ n) ⊎ (n < m)
splitℕ-≤ m n with m ≟ n
... | lt x = inl (<-weaken x)
... | eq x = inl (0 , x)
... | gt x = inr x

splitℕ-< : (m n : ℕ) → (m < n) ⊎ (n ≤ m)
splitℕ-< m n with m ≟ n
... | lt x = inl x
... | eq x = inr (0 , (sym x))
... | gt x = inr (<-weaken x)

≤CaseInduction : {P : ℕ → ℕ → Type ℓ} {n m : ℕ}
  → (n ≤ m → P n m) → (m ≤ n → P n m)
  → P n m
≤CaseInduction {n = n} {m = m} p q with n ≟ m
... | lt x = p (<-weaken x)
... | eq x = p (subst (n ≤_) x ≤-refl)
... | gt x = q (<-weaken x)

<-split : m < suc n → (m < n) ⊎ (m ≡ n)
<-split {n = zero} = inr ∘ snd ∘ m+n≡0→m≡0×n≡0 ∘ snd ∘ pred-≤-pred
<-split {zero} {suc n} = λ _ → inl (suc-≤-suc zero-≤)
<-split {suc m} {suc n} = ⊎.map suc-≤-suc (cong suc) ∘ <-split ∘ pred-≤-pred

≤-split : m ≤ n → (m < n) ⊎ (m ≡ n)
≤-split p = <-split (suc-≤-suc p)

≤→< : m ≤ n → ¬ m ≡ n → m < n
≤→< p q =
  case (≤-split p) of
    λ { (inl r) → r
      ; (inr r) → ⊥.rec (q r) }

≤-suc-≢ : m ≤ suc n → (m ≡ suc n → ⊥ ) → m ≤ n
≤-suc-≢ p ¬q = pred-≤-pred (≤→< p ¬q)

≤-+-split : ∀ n m k → k ≤ n + m → (n ≤ k) ⊎ (m ≤ (n + m) ∸ k)
≤-+-split n m k k≤n+m with n ≟ k
... | eq p = inl (0 , p)
... | lt n<k = inl (<-weaken n<k)
... | gt k<n with m ≟ ((n + m) ∸ k)
... | eq p = inr (0 , p)
... | lt m<n+m∸k = inr (<-weaken m<n+m∸k)
... | gt n+m∸k<m =
      ⊥.rec (¬m<m (transport (λ i → ≤-∸-+-cancel k≤n+m i < +-comm m n i) (<-+-< n+m∸k<m k<n)))

<-asym'-case : Trichotomy m n → ¬ m < n → n ≤ m
<-asym'-case (lt p) q = ⊥.rec (q p)
<-asym'-case (eq p) _ = _ , sym p
<-asym'-case (gt p) _ = <-weaken p

<-asym' : ¬ m < n → n ≤ m
<-asym' = <-asym'-case (_≟_ _ _)

private
  acc-suc : Acc _<_ n → Acc _<_ (suc n)
  acc-suc a
    = acc λ y y<sn
    → case <-split y<sn of λ
    { (inl y<n) → access a y y<n
    ; (inr y≡n) → subst _ (sym y≡n) a
    }

<-wellfounded : WellFounded _<_
<-wellfounded zero = acc λ _ → ⊥.rec ∘ ¬-<-zero
<-wellfounded (suc n) = acc-suc (<-wellfounded n)

<→≢ : n < m → ¬ n ≡ m
<→≢ {n} {m} p q = ¬m<m (subst (_< m) q p)

module _
    (b₀ : ℕ)
    (P : ℕ → Type₀)
    (base : ∀ n → n < suc b₀ → P n)
    (step : ∀ n → P n → P (suc b₀ + n))
  where
  open WFI (<-wellfounded)

  private
    dichotomy : ∀ b n → (n < b) ⊎ (Σ[ m ∈ ℕ ] n ≡ b + m)
    dichotomy b n
      = case n ≟ b return (λ _ → (n < b) ⊎ (Σ[ m ∈ ℕ ] n ≡ b + m)) of λ
      { (lt o) → inl o
      ; (eq p) → inr (0 , p ∙ sym (+-zero b))
      ; (gt (m , p)) → inr (suc m , sym p ∙ +-suc m b ∙ +-comm (suc m) b)
      }

    dichotomy<≡ : ∀ b n → (n<b : n < b) → dichotomy b n ≡ inl n<b
    dichotomy<≡ b n n<b
      = case dichotomy b n return (λ d → d ≡ inl n<b) of λ
      { (inl x) → cong inl (isProp≤ x n<b)
      ; (inr (m , p)) → ⊥.rec (<-asym n<b (m , sym (p ∙ +-comm b m)))
      }

    dichotomy+≡ : ∀ b m n → (p : n ≡ b + m) → dichotomy b n ≡ inr (m , p)
    dichotomy+≡ b m n p
      = case dichotomy b n return (λ d → d ≡ inr (m , p)) of λ
      { (inl n<b) → ⊥.rec (<-asym n<b (m , +-comm m b ∙ sym p))
      ; (inr (m' , q))
      → cong inr (Σ≡Prop (λ x → isSetℕ n (b + x)) (inj-m+ {m = b} (sym q ∙ p)))
      }

    b = suc b₀

    lemma₁ : ∀{x y z} → x ≡ suc z + y → y < x
    lemma₁ {y = y} {z} p = z , +-suc z y ∙ sym p

    subStep : (n : ℕ) → (∀ m → m < n → P m) → (n < b) ⊎ (Σ[ m ∈ ℕ ] n ≡ b + m) → P n
    subStep n _   (inl l) = base n l
    subStep n rec (inr (m , p))
      = transport (cong P (sym p)) (step m (rec m (lemma₁ p)))

    wfStep : (n : ℕ) → (∀ m → m < n → P m) → P n
    wfStep n rec = subStep n rec (dichotomy b n)

    wfStepLemma₀ : ∀ n (n<b : n < b) rec → wfStep n rec ≡ base n n<b
    wfStepLemma₀ n n<b rec = cong (subStep n rec) (dichotomy<≡ b n n<b)

    wfStepLemma₁ : ∀ n rec → wfStep (b + n) rec ≡ step n (rec n (lemma₁ refl))
    wfStepLemma₁ n rec
      = cong (subStep (b + n) rec) (dichotomy+≡ b n (b + n) refl)
      ∙ transportRefl _

  +induction : ∀ n → P n
  +induction = induction wfStep

  +inductionBase : ∀ n → (l : n < b) → +induction n ≡ base n l
  +inductionBase n l = induction-compute wfStep n ∙ wfStepLemma₀ n l _

  +inductionStep : ∀ n → +induction (b + n) ≡ step n (+induction n)
  +inductionStep n = induction-compute wfStep (b + n) ∙ wfStepLemma₁ n _

module <-Reasoning where
  -- TODO: would it be better to mirror the way it is done in the agda-stdlib?
  infixr 2 _<⟨_⟩_ _≤<⟨_⟩_ _≤⟨_⟩_ _<≤⟨_⟩_ _≡<⟨_⟩_ _≡≤⟨_⟩_ _<≡⟨_⟩_ _≤≡⟨_⟩_
  _<⟨_⟩_ : ∀ k → k < n → n < m → k < m
  _ <⟨ p ⟩ q = <-trans p q

  _≤<⟨_⟩_ : ∀ k → k ≤ n → n < m → k < m
  _ ≤<⟨ p ⟩ q = ≤<-trans p q

  _≤⟨_⟩_ : ∀ k → k ≤ n → n ≤ m → k ≤ m
  _ ≤⟨ p ⟩ q = ≤-trans p q

  _<≤⟨_⟩_ : ∀ k → k < n → n ≤ m → k < m
  _ <≤⟨ p ⟩ q = <≤-trans p q

  _≡≤⟨_⟩_ : ∀ k → k ≡ l → l ≤ m → k ≤ m
  _ ≡≤⟨ p ⟩ q = subst (λ k → k ≤ _) (sym p) q

  _≡<⟨_⟩_ : ∀ k → k ≡ l → l < m → k < m
  _ ≡<⟨ p ⟩ q = _ ≡≤⟨ cong suc p ⟩ q

  _≤≡⟨_⟩_ : ∀ k → k ≤ l → l ≡ m → k ≤ m
  _ ≤≡⟨ p ⟩ q = subst (λ l → _ ≤ l) q p

  _<≡⟨_⟩_ : ∀ k → k < l → l ≡ m → k < m
  _ <≡⟨ p ⟩ q = _ ≤≡⟨ p ⟩ q


-- Some lemmas about ∸
suc∸-fst : (n m : ℕ) → m < n → suc (n ∸ m) ≡ (suc n) ∸ m
suc∸-fst zero zero p = refl
suc∸-fst zero (suc m) p = ⊥.rec (¬-<-zero p)
suc∸-fst (suc n) zero p = refl
suc∸-fst (suc n) (suc m) p = (suc∸-fst n m (pred-≤-pred p))

n∸m≡0 : (n m : ℕ) → n ≤ m → (n ∸ m) ≡ 0
n∸m≡0 zero zero p = refl
n∸m≡0 (suc n) zero p = ⊥.rec (¬-<-zero p)
n∸m≡0 zero (suc m) p = refl
n∸m≡0 (suc n) (suc m) p = n∸m≡0 n m (pred-≤-pred p)

n∸n≡0 : (n : ℕ) → n ∸ n ≡ 0
n∸n≡0 zero = refl
n∸n≡0 (suc n) = n∸n≡0 n

n∸l>0 : (n l : ℕ) → (l < n) → 0 < (n ∸ l)
n∸l>0  zero    zero   r = ⊥.rec (¬-<-zero r)
n∸l>0  zero   (suc l) r = ⊥.rec (¬-<-zero r)
n∸l>0 (suc n)  zero   r = suc-≤-suc zero-≤
n∸l>0 (suc n) (suc l) r = n∸l>0 n l (pred-≤-pred r)

-- automation

≤-solver-type : (m n : ℕ) → Trichotomy m n → Type
≤-solver-type m n (lt p) = m ≤ n
≤-solver-type m n (eq p) = m ≤ n
≤-solver-type m n (gt p) = n < m

≤-solver-case : (m n : ℕ) → (p : Trichotomy m n) → ≤-solver-type m n p
≤-solver-case m n (lt p) = <-weaken p
≤-solver-case m n (eq p) = _ , p
≤-solver-case m n (gt p) = p

≤-solver : (m n : ℕ) → ≤-solver-type m n (m ≟ n)
≤-solver m n = ≤-solver-case m n (m ≟ n)



-- inductive order relation taken from agda-stdlib
data _≤'_ : ℕ → ℕ → Type where
  z≤ : ∀ {n} → zero ≤' n
  s≤s : ∀ {m n} → m ≤' n → suc m ≤' suc n

_<'_ : ℕ → ℕ → Type
m <' n = suc m ≤' n

-- Smart constructors of _<_
pattern z<s {n}         = s≤s (z≤ {n})
pattern s<s {m} {n} m<n = s≤s {m} {n} m<n

¬-<'-zero : ¬ m <' 0
¬-<'-zero {zero} ()
¬-<'-zero {suc m} ()

≤'Dec : ∀ m n → Dec (m ≤' n)
≤'Dec zero n = yes z≤
≤'Dec (suc m) zero = no ¬-<'-zero
≤'Dec (suc m) (suc n) with ≤'Dec m n
... | yes m≤'n = yes (s≤s m≤'n)
... | no m≰'n = no λ { (s≤s m≤'n) → m≰'n m≤'n }

≤'IsPropValued : ∀ m n → isProp (m ≤' n)
≤'IsPropValued zero n z≤ z≤ = refl
≤'IsPropValued (suc m) zero ()
≤'IsPropValued (suc m) (suc n) (s≤s x) (s≤s y) = cong s≤s (≤'IsPropValued m n x y)

≤-∸-≤ : ∀ m n l → m ≤ n → m ∸ l ≤ n ∸ l
≤-∸-≤  m       n       zero   r = r
≤-∸-≤  zero    zero   (suc l) r = ≤-refl
≤-∸-≤  zero   (suc n) (suc l) r = (n ∸ l) , (+-zero _)
≤-∸-≤ (suc m)  zero   (suc l) r = ⊥.rec (¬-<-zero r)
≤-∸-≤ (suc m) (suc n) (suc l) r = ≤-∸-≤ m n l (pred-≤-pred r)

<-∸-< : ∀ m n l → m < n → l < n → m ∸ l < n ∸ l
<-∸-<  m       n       zero   r q = r
<-∸-<  zero    zero   (suc l) r q = ⊥.rec (¬-<-zero r)
<-∸-<  zero   (suc n) (suc l) r q = n∸l>0 (suc n) (suc l) q
<-∸-< (suc m)  zero   (suc l) r q = ⊥.rec (¬-<-zero r)
<-∸-< (suc m) (suc n) (suc l) r q = <-∸-< m n l (pred-≤-pred r) (pred-≤-pred q)

≤-∸-≥ : ∀ n l k → l ≤ k → n ∸ k ≤ n ∸ l
≤-∸-≥ n  zero    zero   r = ≤-refl
≤-∸-≥ n  zero   (suc k) r = ∸-≤ n (suc k)
≤-∸-≥ n (suc l)  zero   r = ⊥.rec (¬-<-zero r)
≤-∸-≥  zero   (suc l) (suc k) r = ≤-refl
≤-∸-≥ (suc n) (suc l) (suc k) r = ≤-∸-≥ n l k (pred-≤-pred r)
