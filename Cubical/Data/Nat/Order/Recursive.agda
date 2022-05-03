{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.Recursive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties

open import Cubical.Induction.WellFounded

open import Cubical.Relation.Nullary

infix 4 _≤_ _<_

_≤_ : ℕ → ℕ → Type₀
zero ≤ _ = Unit
suc m ≤ zero = ⊥
suc m ≤ suc n = m ≤ n

_<_ : ℕ → ℕ → Type₀
m < n = suc m ≤ n

_≤?_ : (m n : ℕ) → Dec (m ≤ n)
zero  ≤? _     = yes tt
suc m ≤? zero  = no λ ()
suc m ≤? suc n = m ≤? n

data Trichotomy (m n : ℕ) : Type₀ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

private
  variable
    ℓ : Level
    R : Type ℓ
    P : ℕ → Type ℓ
    k l m n : ℕ

isProp≤ : isProp (m ≤ n)
isProp≤ {zero} = isPropUnit
isProp≤ {suc m} {zero}  = isProp⊥
isProp≤ {suc m} {suc n} = isProp≤ {m} {n}

≤-k+ : m ≤ n → k + m ≤ k + n
≤-k+ {k = zero}  m≤n = m≤n
≤-k+ {k = suc k} m≤n = ≤-k+ {k = k} m≤n

≤-+k : m ≤ n → m + k ≤ n + k
≤-+k {m} {n} {k} m≤n
  = transport (λ i → +-comm k m i ≤ +-comm k n i) (≤-k+ {m} {n} {k} m≤n)

≤-refl : ∀ m → m ≤ m
≤-refl zero = _
≤-refl (suc m) = ≤-refl m

≤-trans : k ≤ m → m ≤ n → k ≤ n
≤-trans {zero} _ _ = _
≤-trans {suc k} {suc m} {suc n} = ≤-trans {k} {m} {n}

≤-antisym : m ≤ n → n ≤ m → m ≡ n
≤-antisym {zero} {zero} _ _ = refl
≤-antisym {suc m} {suc n} m≤n n≤m = cong suc (≤-antisym m≤n n≤m)

≤-k+-cancel : k + m ≤ k + n → m ≤ n
≤-k+-cancel {k =  zero} m≤n = m≤n
≤-k+-cancel {k = suc k} m≤n = ≤-k+-cancel {k} m≤n

≤-+k-cancel : m + k ≤ n + k → m ≤ n
≤-+k-cancel {m} {k} {n}
  = ≤-k+-cancel {k} {m} {n} ∘ transport λ i → +-comm m k i ≤ +-comm n k i

¬m<m : ¬ m < m
¬m<m {suc m} = ¬m<m {m}

≤0→≡0 : n ≤ 0 → n ≡ 0
≤0→≡0 {zero} _ = refl

¬m+n<m : ¬ m + n < m
¬m+n<m {suc m} = ¬m+n<m {m}

<-weaken : m < n → m ≤ n
<-weaken {zero} _ = _
<-weaken {suc m} {suc n} = <-weaken {m}

<-trans : k < m → m < n → k < n
<-trans {k} {m} {n} k<m m<n
  = ≤-trans {suc k} {m} {n} k<m (<-weaken {m} m<n)

<-asym : m < n → ¬ n < m
<-asym {m} m<n n<m = ¬m<m {m} (<-trans {m} {_} {m} m<n n<m)

<→≢ : n < m → ¬ n ≡ m
<→≢ {n} {m} p q = ¬m<m {m = m} (subst {x = n} (_< m) q p)

Trichotomy-suc : Trichotomy m n → Trichotomy (suc m) (suc n)
Trichotomy-suc (lt m<n) = lt m<n
Trichotomy-suc (eq m≡n) = eq (cong suc m≡n)
Trichotomy-suc (gt n<m) = gt n<m

_≟_ : ∀ m n → Trichotomy m n
zero  ≟ zero = eq refl
zero  ≟ suc n = lt _
suc m ≟ zero = gt _
suc m ≟ suc n = Trichotomy-suc (m ≟ n)

k≤k+n : ∀ k → k ≤ k + n
k≤k+n zero    = _
k≤k+n (suc k) = k≤k+n k

n≤k+n : ∀ n → n ≤ k + n
n≤k+n {k} n = transport (λ i → n ≤ +-comm n k i) (k≤k+n n)

≤-split : m ≤ n → (m < n) ⊎ (m ≡ n)
≤-split {zero} {zero} m≤n = inr refl
≤-split {zero} {suc n} m≤n = inl _
≤-split {suc m} {suc n} m≤n
  = Sum.map (idfun _) (cong suc) (≤-split {m} {n} m≤n)

module WellFounded where
  wf-< : WellFounded _<_
  wf-rec-< : ∀ n → WFRec _<_ (Acc _<_) n

  wf-< n = acc (wf-rec-< n)

  wf-rec-< (suc n) m m≤n with ≤-split {m} {n} m≤n
  ... | inl m<n = wf-rec-< n m m<n
  ... | inr m≡n = subst⁻ (Acc _<_) m≡n (wf-< n)

wf-elim : (∀ n → (∀ m → m < n → P m) → P n) → ∀ n → P n
wf-elim = WFI.induction WellFounded.wf-<

wf-rec : (∀ n → (∀ m → m < n → R) → R) → ℕ → R
wf-rec {R = R} = wf-elim {P = λ _ → R}

module Minimal where
  Least : ∀{ℓ} → (ℕ → Type ℓ) → (ℕ → Type ℓ)
  Least P m = P m × (∀ n → n < m → ¬ P n)

  isPropLeast : (∀ m → isProp (P m)) → ∀ m → isProp (Least P m)
  isPropLeast pP m
    = isPropΣ (pP m) (λ _ → isPropΠ3 λ _ _ _ → isProp⊥)

  Least→ : Σ _ (Least P) → Σ _ P
  Least→ = map-snd fst

  search
    : (∀ m → Dec (P m))
    → ∀ n → (Σ[ m ∈ ℕ ] Least P m) ⊎ (∀ m → m < n → ¬ P m)
  search dec zero = inr (λ _ b _ → b)
  search {P = P} dec (suc n) with search dec n
  ... | inl tup = inl tup
  ... | inr ¬P<n with dec n
  ... | yes Pn = inl (n , Pn , ¬P<n)
  ... | no ¬Pn = inr λ m m≤n
      → case ≤-split m≤n of λ where
          (inl m<n) → ¬P<n m m<n
          (inr m≡n) → subst⁻ (¬_ ∘ P) m≡n ¬Pn

  →Least : (∀ m → Dec (P m)) → Σ _ P → Σ _ (Least P)
  →Least dec (n , Pn) with search dec n
  ... | inl least = least
  ... | inr ¬P<n  = n , Pn , ¬P<n

  Least-unique : ∀ m n → Least P m → Least P n → m ≡ n
  Least-unique m n (Pm , ¬P<m) (Pn , ¬P<n) with m ≟ n
  ... | lt m<n = Empty.rec (¬P<n m m<n Pm)
  ... | eq m≡n = m≡n
  ... | gt n<m = Empty.rec (¬P<m n n<m Pn)

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
