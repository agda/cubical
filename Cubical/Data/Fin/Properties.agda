{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Fin.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Function
open import Cubical.Foundations.Embedding
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Logic using (pequivToPath)

open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Induction.WellFounded

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

expand : ∀{k} → (Fin k × ℕ) → ℕ
expand {k} (f , o) = o * k + toℕ f

Reduction : ℕ → ℕ → Set
Reduction k n = Σ[ tup ∈ Fin k × ℕ ] expand tup ≡ n

Reduction+k : (k n : ℕ) → Reduction k n → Reduction k (k + n)
Reduction+k k n ((f , o) , p)
  = (f , suc o) , sym (+-assoc k (o * k) (toℕ f)) ∙ cong (k +_) p

Reduction-k : (k n : ℕ) → Reduction k (k + n) → Reduction k n
Reduction-k k n (((m , m<k) , zero) , p) = ⊥-elim (<-asym m<k k≤m)
  where
  k≤m : k ≤ m
  k≤m = n , +-comm n k ∙ sym p
Reduction-k k n ((f , suc o) , p) = ((f , o) , inj-m+ (+-assoc k (o * k) (toℕ f) ∙ p))

private
  expand-lemma
    : ∀ {k} (f1 f2 : Fin k) o1 o2
    → expand (f1 , suc o1) ≡ expand (f2 , suc o2)
    → expand (f1 , o1) ≡ expand (f2 , o2)
  expand-lemma {k} f1 f2 o1 o2 p
    = inj-m+ {m = k} (+-assoc k _ _ ∙ p ∙ sym (+-assoc k _ _))

  injExpand
    : ∀ {k}
    → {t1 t2 : Fin k × ℕ}
    → expand t1 ≡ expand t2
    → t1 ≡ t2
  injExpand {zero} {f , _} _ = ⊥-elim (¬Fin0 f)
  injExpand {k} {f1 , zero} {f2 , zero} p = cong (_, zero) (toℕ-injective p)
  injExpand {k} {(n , n<k) , zero} {f2 , suc o2} p = ⊥-elim (<-asym n<k k≤n)
    where
    k≤n : k ≤ n
    k≤n = o2 * k + toℕ f2
        , +-comm (o2 * k + toℕ f2) k ∙ +-assoc k (o2 * k) (toℕ f2) ∙ sym p
  injExpand {k} {f1 , suc o1} {(n , n<k) , zero} p = ⊥-elim (<-asym n<k k≤n)
    where
    k≤n : k ≤ n
    k≤n = o1 * k + toℕ f1
        , +-comm (o1 * k + toℕ f1) k ∙ +-assoc k (o1 * k) (toℕ f1) ∙ p
  injExpand {k} {f1 , suc o1} {f2 , suc o2}
    = cong psuc ∘ injExpand {k} {f1 , o1} {f2 , o2} ∘ expand-lemma f1 f2 o1 o2
    where
    psuc : Fin k × ℕ → Fin k × ℕ
    psuc (f , o) = f , suc o

  embExpand
    : ∀ k → isEmbedding (expand {k})
  embExpand zero = ⊥-elim ∘ ¬Fin0 ∘ fst
  embExpand (suc k)
    = injEmbedding (isOfHLevelΣ 2 isSetFin λ _ → isSetℕ) isSetℕ injExpand

isPropReduction : ∀{k n} → isProp (Reduction k n)
isPropReduction {k} {n} = isEmbedding→isPropFiber (embExpand k) n

Reduction≡ : ∀{k n} → Reduction k n ≡ Reduction k (k + n)
Reduction≡ {k} {n}
  = pequivToPath
      {Reduction k n , isPropReduction}
      {Reduction k (k + n) , isPropReduction}
      (Reduction+k k n)
      (Reduction-k k n)

Reduction⇒ : ∀{k m n} → k + m ≡ n → Reduction k m ≡ Reduction k n
Reduction⇒ {k} p = Reduction≡ ∙ (λ i → Reduction k (p i))

reduce : ∀ k₀ n → Reduction (suc k₀) n
reduce k₀ n = induction step n
  where
  k : ℕ
  k = suc k₀

  open WFI (<-wellfounded)
  Goal : ∀{A : Set} → ℕ → A → Set
  Goal r _ = Reduction k r

  lemma : ∀{x y z} → x ≡ suc z + y → y < x
  lemma {y = y} {z} p = z , +-suc z y ∙ sym p

  step : (n : ℕ) → (∀ m → m < n → Reduction k m) → Reduction k n
  step n rec
    = case dichotomy k n return Goal n of λ
    { (inl l) → ((n , l) , 0) , refl
    ; (inr (m , p)) → transport (Reduction⇒ (sym p)) (rec m (lemma p))
    }

isContrReduction : ∀{k n} → isContr (Reduction (suc k) n)
isContrReduction {k} {n} = inhProp→isContr (reduce k n) isPropReduction
