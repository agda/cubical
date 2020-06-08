{-# OPTIONS --cubical --no-exact-split --safe #-}
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

infix 4 _≤_ _<_

_≤_ : ℕ → ℕ → Type₀
m ≤ n = Σ[ k ∈ ℕ ] k + m ≡ n

_<_ : ℕ → ℕ → Type₀
m < n = suc m ≤ n

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

m≤n-isProp : isProp (m ≤ n)
m≤n-isProp {m} {n} (k , p) (l , q)
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

≤-k+ : m ≤ n → k + m ≤ k + n
≤-k+ {m} {n} {k}
  = subst (_≤ k + n) (+-comm m k)
  ∘ subst (m + k ≤_) (+-comm n k)
  ∘ ≤-+k

pred-≤-pred : suc m ≤ suc n → m ≤ n
pred-≤-pred (k , p) = k , injSuc ((sym (+-suc k _)) ∙ p)

≤-refl : m ≤ m
≤-refl = 0 , refl

≤-suc : m ≤ n → m ≤ suc n
≤-suc (k , p) = suc k , cong suc p

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
≤<-trans {l} {m} {n} (i , p) (j , q) = (j + i) , reason
  where
  reason : j + i + suc l ≡ n
  reason = j + i + suc l ≡⟨ sym (+-assoc j i (suc l)) ⟩
           j + (i + suc l) ≡⟨ cong (j +_) (+-suc i l) ⟩
           j + (suc (i + l)) ≡⟨ cong (_+_ j ∘ suc) p ⟩
           j + suc m ≡⟨ q ⟩
           n ∎

<≤-trans : l < m → m ≤ n → l < n
<≤-trans {l} {m} {n} (i , p) (j , q) = j + i , reason
  where
  reason : j + i + suc l ≡ n
  reason = j + i + suc l ≡⟨ sym (+-assoc j i (suc l)) ⟩
           j + (i + suc l) ≡⟨ cong (j +_) p ⟩
           j + m ≡⟨ q ⟩
           n ∎

<-trans : l < m → m < n → l < n
<-trans p = ≤<-trans (<-weaken p)

<-asym : m < n → ¬ n ≤ m
<-asym m<n = ¬m<m ∘ <≤-trans m<n

Trichotomy-suc : Trichotomy m n → Trichotomy (suc m) (suc n)
Trichotomy-suc (lt m<n) = lt (suc-≤-suc m<n)
Trichotomy-suc (eq m=n) = eq (cong suc m=n)
Trichotomy-suc (gt n<m) = gt (suc-≤-suc n<m)

_≟_ : ∀ m n → Trichotomy m n
zero ≟ zero = eq refl
zero ≟ suc n = lt (n , +-comm n 1)
suc m ≟ zero = gt (m , +-comm m 1)
suc m ≟ suc n = Trichotomy-suc (m ≟ n)

<-split : m < suc n → (m < n) ⊎ (m ≡ n)
<-split {n = zero} = inr ∘ snd ∘ m+n≡0→m≡0×n≡0 ∘ snd ∘ pred-≤-pred
<-split {zero} {suc n} = λ _ → inl (suc-≤-suc zero-≤)
<-split {suc m} {suc n} = ⊎.map suc-≤-suc (cong suc) ∘ <-split ∘ pred-≤-pred

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
      { (inl x) → cong inl (m≤n-isProp x n<b)
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
