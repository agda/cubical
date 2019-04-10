{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Fin.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Embedding
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

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

expand : ℕ → ℕ → ℕ → ℕ
expand 0 k m = m
expand (suc o) k m = k + expand o k m

expand≡
  : ∀ k m o → expand o k m ≡ o * k + m
expand≡ k m zero = refl
expand≡ k m (suc o)
  = cong (k +_) (expand≡ k m o) ∙ +-assoc k (o * k) m

expand× : ∀{k} → (Fin k × ℕ) → ℕ
expand× {k} (f , o) = expand o k (toℕ f)

private
  lemma₀ : ∀{k m n r} → r ≡ n → k + m ≡ n → k ≤ r
  lemma₀ {k = k} {m} p q = m , +-comm m k ∙ q ∙ sym p

  expandInj : ∀ k → {t1 t2 : Fin (suc k) × ℕ} → expand× t1 ≡ expand× t2 → t1 ≡ t2
  expandInj k {f1 , zero} {f2 , zero} p i
    = toℕ-injective {fj = f1} {f2} p i , zero
  expandInj k {f1 , suc o1} {(r , r<sk) , zero} p
    = ⊥-elim (<-asym r<sk (lemma₀ refl p))
  expandInj k {(r , r<sk) , zero} {f2 , suc o2} p
    = ⊥-elim (<-asym r<sk (lemma₀ refl (sym p)))
  expandInj k {f1 , suc o1} {f2 , suc o2}
    = cong (λ { (f , o) → (f , suc o) })
    ∘ expandInj k {f1 , o1} {f2 , o2}
    ∘ inj-m+ {suc k}

  expandEmb : ∀ k → isEmbedding (expand× {k})
  expandEmb 0 = ⊥-elim ∘ ¬Fin0 ∘ fst
  expandEmb (suc k)
    = injEmbedding (isOfHLevelΣ 2 isSetFin (λ _ → isSetℕ)) isSetℕ (expandInj k)

Reduction : ℕ → ℕ → Set
Reduction k n = Σ[ tup ∈ Fin k × ℕ ] expand× tup ≡ n

extract : ∀{k n} → Reduction k n → Fin k
extract = fst ∘ fst

isPropReduction : ∀ k n → isProp (Reduction k n)
isPropReduction k = isEmbedding→isPropFiber (expandEmb k)

Fin→Reduction : ∀{k} → (f : Fin k) → Reduction k (toℕ f)
Fin→Reduction f = (f , 0) , refl

Reduction+k : (k n : ℕ) → Reduction k n → Reduction k (k + n)
Reduction+k k n ((f , o) , p)
  = (f , suc o) , cong (k +_) p

Reduction-k : (k n : ℕ) → Reduction k (k + n) → Reduction k n
Reduction-k k n (((r , r<k) , zero) , p) = ⊥-elim (<-asym r<k (lemma₀ p refl))
Reduction-k k n ((f , suc o) , p)
  = ((f , o) , inj-m+ p)

Reduction+k-k
  : (k n : ℕ)
  → (R : Reduction k (k + n))
  → Reduction+k k n (Reduction-k k n R) ≡ R
Reduction+k-k k n (((r , r<k) , zero) , p) = ⊥-elim (<-asym r<k (lemma₀ p refl))
Reduction+k-k k n ((f , suc o) , p)
  = subtypeEquality (λ tup → isSetℕ (expand× tup) (k + n)) _ _ refl

Reduction-k+k
  : (k n : ℕ)
  → (R : Reduction k n)
  → Reduction-k k n (Reduction+k k n R) ≡ R
Reduction-k+k k n ((f , o) , p)
  = subtypeEquality (λ tup → isSetℕ (expand× tup) n) _ _ refl

private
  Reduction≃ : ∀ k n → Reduction k n ≃ Reduction k (k + n)
  Reduction≃ k n
    = Reduction+k k n
    , isoToIsEquiv (iso (Reduction+k k n) (Reduction-k k n)
                        (Reduction+k-k k n) (Reduction-k+k k n))

Reduction≡ : ∀ k n → Reduction k n ≡ Reduction k (k + n)
Reduction≡ k n = ua (Reduction≃ k n)

module Reduce (k₀ : ℕ) where
  k : ℕ
  k = suc k₀

  base : ∀ n (n<k : n < k) → Reduction k n
  base n n<k = Fin→Reduction (n , n<k)

  step : ∀ n → Reduction k n → Reduction k (k + n)
  step n = transport (Reduction≡ k n)

  reduce : ∀ n → Reduction k n
  reduce = +induction k₀ (Reduction k) base step

  reduce≡
    : ∀ n → transport (Reduction≡ k n) (reduce n) ≡ reduce (k + n)
  reduce≡ n
    = sym (+inductionStep k₀ _ base step n)

  reduceP
    : ∀ n → PathP (λ i → Reduction≡ k n i) (reduce n) (reduce (k + n))
  reduceP n = toPathP (reduce≡ n)

open Reduce using (reduce; reduce≡) public

private
  lemma₅
    : ∀ k n (R : Reduction k n)
    →  extract R ≡ extract (transport (Reduction≡ k n) R)
  lemma₅ k n = sym ∘ cong extract ∘ uaβ (Reduction≃ k n)

extract≡ : ∀ k n → extract (reduce k n) ≡ extract (reduce k (suc k + n))
extract≡ k n
  = lemma₅ (suc k) n (reduce k n) ∙ cong extract (Reduce.reduce≡ k n)

isContrReduction : ∀{k n} → isContr (Reduction (suc k) n)
isContrReduction {k} {n} = inhProp→isContr (reduce k n) (isPropReduction (suc k) n)
