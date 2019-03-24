{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Fin.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Induction.WellFounded

private
  _×_ : Set → Set → Set
  A × B = Σ A λ _ → B

Fin0-isProp : isProp (Fin 0)
Fin0-isProp = ⊥-elim ∘ ¬Fin0

Fin1-isContr : isContr (Fin 1)
Fin1-isContr
  = fzero , λ
  { (zero , _) → toℕ-injective refl
  ; (suc k , sk<1) → ⊥-elim (¬-<-zero (pred-≤-pred sk<1))
  }

isSetFin : ∀{k} → isSet (Fin k)
isSetFin {k} = isOfHLevelΣ 2 isSetℕ (λ _ → isProp→isSet m≤n-isProp)

private
  dichotomy : ∀ k n → (n < k) ⊎ (Σ[ m ∈ ℕ ] n ≡ k + m)
  dichotomy k n
    = case n ≟ k return (λ _ → (n < k) ⊎ (Σ[ m ∈ ℕ ] n ≡ k + m)) of λ
    { (lt o) → inl o
    ; (eq p) → inr (0 , p ∙ sym (+-zero k))
    ; (gt (m , p)) → inr (suc m , sym p ∙ +-suc m k ∙ +-comm (suc m) k)
    }

  dichotomy+≡ : ∀ k m n → (p : n ≡ k + m) → dichotomy k n ≡ inr (m , p)
  dichotomy+≡ k m n p
    = case dichotomy k n return (λ d → d ≡ inr (m , p)) of λ
    { (inl n<k) → ⊥-elim (<-asym n<k (m , +-comm m k ∙ sym p))
    ; (inr (m' , q))
    → cong inr (subtypeEquality
        (λ x → isSetℕ n (k + x)) (m' , q) (m , p) (inj-m+ {m = k} (sym q ∙ p)))
    }

expand : ∀{k} → (Fin k × ℕ) → ℕ
expand {k} (f , o) = o * k + toℕ f

Reduction : ℕ → ℕ → Set
Reduction k n = Σ[ tup ∈ Fin k × ℕ ] expand tup ≡ n

Reduction+k : (k m n : ℕ) → k + m ≡ n → Reduction k m → Reduction k n
Reduction+k k m n q ((f , o) , p)
  = (f , suc o) , sym (+-assoc k (o * k) (toℕ f)) ∙ cong (k +_) p ∙ q

Reduction-k : (k m n : ℕ) → k + m ≡ n → Reduction k n → Reduction k m
Reduction-k k m n q (((r , r<k) , zero) , p) = ⊥-elim (<-asym r<k k≤r)
  where
  k≤r : k ≤ r
  k≤r = m , +-comm m k ∙ q ∙ sym p
Reduction-k k m n q ((f , suc o) , p)
  = ((f , o) , inj-m+ (+-assoc k (o * k) (toℕ f) ∙ p ∙ sym q))

Reduction+k-k
  : (k m n : ℕ)
  → (q : k + m ≡ n)
  → (R : Reduction k n)
  → Reduction+k k m n q (Reduction-k k m n q R) ≡ R
Reduction+k-k k m n q (((r , r<k) , zero) , p) = ⊥-elim (<-asym r<k k≤r)
  where
  k≤r : k ≤ r
  k≤r = m , +-comm m k ∙ q ∙ sym p
Reduction+k-k k m n q ((f , suc o) , p)
  = subtypeEquality (λ tup → isSetℕ (expand tup) n) _ _ refl

Reduction-k+k
  : (k m n : ℕ)
  → (q : k + m ≡ n)
  → (R : Reduction k m)
  → Reduction-k k m n q (Reduction+k k m n q R) ≡ R
Reduction-k+k k m n q ((f , o) , p)
  = subtypeEquality (λ tup → isSetℕ (expand tup) m) _ _ refl

Reduction≡ : ∀ k m n (q : k + m ≡ n) → Reduction k m ≡ Reduction k n
Reduction≡ k m n q
  = isoToPath (iso (Reduction+k k m n q) (Reduction-k k m n q)
                   (Reduction+k-k k m n q) (Reduction-k+k k m n q))

module _ (k₀ : ℕ) where
  open WFI (<-wellfounded)

  private
    k : ℕ
    k = suc k₀

    Goal : ∀{A : Set} → ℕ → A → Set
    Goal r _ = Reduction k r

    lemma₁ : ∀{x y z} → x ≡ suc z + y → y < x
    lemma₁ {y = y} {z} p = z , +-suc z y ∙ sym p

    subStep
      : (n : ℕ)
      → (∀ m → m < n → Reduction k m)
      → (n < k) ⊎ (Σ[ m ∈ ℕ ] n ≡ k + m)
      → Reduction k n
    subStep n rec (inl l) = ((n , l) , 0) , refl
    subStep n rec (inr (m , p))
      = transport (Reduction≡ k m n (sym p)) (rec m (lemma₁ p))

    step : (n : ℕ) → (∀ m → m < n → Reduction k m) → Reduction k n
    step n rec = subStep n rec (dichotomy k n)

  reduce : ∀ n → Reduction (suc k₀) n
  reduce = induction step

  private
    lemma₂ : ∀ n → step n (λ m _ → reduce m) ≡ reduce n
    lemma₂ = sym ∘ induction-compute step

    lemma₃
      : ∀ m n
      → (p : k + m ≡ n)
      → (rec : ∀ m → m < n → Reduction k m)
      →  transport (Reduction≡ k m n p) (rec m (lemma₁ (sym p))) ≡ step n rec
    lemma₃ m n p rec = (sym ∘ cong (subStep n rec)) (dichotomy+≡ k m n (sym p))

    lemma₄
      : ∀ m n
      → (p : k + m ≡ n)
      → transport (Reduction≡ k m n p) (reduce m) ≡ reduce n
    lemma₄ m n p
      = lemma₃ m n p (λ m _ → reduce m) ∙ lemma₂ n

  reduce≡
    : ∀ m n (p : k + m ≡ n)
    → PathP (λ i → Reduction≡ k m n p i) (reduce m) (reduce n)
  reduce≡ m n p = toPathP (lemma₄ m n p)

-- isContrReduction : ∀{k n} → isContr (Reduction (suc k) n)
-- isContrReduction {k} {n} = inhProp→isContr (reduce k n) isPropReduction
