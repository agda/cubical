{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Fin.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Embedding
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Induction.WellFounded

private
  -- Σ is more convenient than the inductive ×, but I don't
  -- want to have to write λ_→ all over.
  _×_ : Type₀ → Type₀ → Type₀
  A × B = Σ A λ _ → B

-- Fin 0 is empty, and thus a proposition.
Fin0-isProp : isProp (Fin 0)
Fin0-isProp = ⊥-elim ∘ ¬Fin0

-- Fin 1 has only one value.
Fin1-isContr : isContr (Fin 1)
Fin1-isContr
  = fzero , λ
  { (zero , _) → toℕ-injective refl
  ; (suc k , sk<1) → ⊥-elim (¬-<-zero (pred-≤-pred sk<1))
  }

-- Regardless of k, Fin k is a set.
isSetFin : ∀{k} → isSet (Fin k)
isSetFin {k} = isOfHLevelΣ 2 isSetℕ (λ _ → isProp→isSet m≤n-isProp)

-- Helper function for the reduction procedure below.
--
-- If n = expand o k m, then n is congruent to m modulo k.
expand : ℕ → ℕ → ℕ → ℕ
expand 0 k m = m
expand (suc o) k m = k + expand o k m

expand≡ : ∀ k m o → expand o k m ≡ o * k + m
expand≡ k m zero = refl
expand≡ k m (suc o)
  = cong (k +_) (expand≡ k m o) ∙ +-assoc k (o * k) m

-- Expand a pair. This is useful because the whole function is
-- injective.
expand× : ∀{k} → (Fin k × ℕ) → ℕ
expand× {k} (f , o) = expand o k (toℕ f)

private
  lemma₀ : ∀{k m n r} → r ≡ n → k + m ≡ n → k ≤ r
  lemma₀ {k = k} {m} p q = m , +-comm m k ∙ q ∙ sym p

  expand×Inj : ∀ k → {t1 t2 : Fin (suc k) × ℕ} → expand× t1 ≡ expand× t2 → t1 ≡ t2
  expand×Inj k {f1 , zero} {f2 , zero} p i
    = toℕ-injective {fj = f1} {f2} p i , zero
  expand×Inj k {f1 , suc o1} {(r , r<sk) , zero} p
    = ⊥-elim (<-asym r<sk (lemma₀ refl p))
  expand×Inj k {(r , r<sk) , zero} {f2 , suc o2} p
    = ⊥-elim (<-asym r<sk (lemma₀ refl (sym p)))
  expand×Inj k {f1 , suc o1} {f2 , suc o2}
    = cong (λ { (f , o) → (f , suc o) })
    ∘ expand×Inj k {f1 , o1} {f2 , o2}
    ∘ inj-m+ {suc k}

  expand×Emb : ∀ k → isEmbedding (expand× {k})
  expand×Emb 0 = ⊥-elim ∘ ¬Fin0 ∘ fst
  expand×Emb (suc k)
    = injEmbedding (isOfHLevelΣ 2 isSetFin (λ _ → isSetℕ)) isSetℕ (expand×Inj k)

-- A Residue is a family of types representing evidence that a
-- natural is congruent to a value of a finite type.
Residue : ℕ → ℕ → Type₀
Residue k n = Σ[ tup ∈ Fin k × ℕ ] expand× tup ≡ n

extract : ∀{k n} → Residue k n → Fin k
extract = fst ∘ fst

-- There is at most one canonical finite value congruent to each
-- natural.
isPropResidue : ∀ k n → isProp (Residue k n)
isPropResidue k = isEmbedding→hasPropFibers (expand×Emb k)

-- A value of a finite type is its own residue.
Fin→Residue : ∀{k} → (f : Fin k) → Residue k (toℕ f)
Fin→Residue f = (f , 0) , refl

-- Fibers of numbers that differ by k are equivalent in a more obvious
-- way than via the fact that they are propositions.
Residue+k : (k n : ℕ) → Residue k n → Residue k (k + n)
Residue+k k n ((f , o) , p) = (f , suc o) , cong (k +_) p

Residue-k : (k n : ℕ) → Residue k (k + n) → Residue k n
Residue-k k n (((r , r<k) , zero) , p) = ⊥-elim (<-asym r<k (lemma₀ p refl))
Residue-k k n ((f , suc o) , p) = ((f , o) , inj-m+ p)

Residue+k-k
  : (k n : ℕ)
  → (R : Residue k (k + n))
  → Residue+k k n (Residue-k k n R) ≡ R
Residue+k-k k n (((r , r<k) , zero) , p) = ⊥-elim (<-asym r<k (lemma₀ p refl))
Residue+k-k k n ((f , suc o) , p)
  = ΣProp≡ (λ tup → isSetℕ (expand× tup) (k + n)) refl

Residue-k+k
  : (k n : ℕ)
  → (R : Residue k n)
  → Residue-k k n (Residue+k k n R) ≡ R
Residue-k+k k n ((f , o) , p)
  = ΣProp≡ (λ tup → isSetℕ (expand× tup) n) refl

private
  Residue≃ : ∀ k n → Residue k n ≃ Residue k (k + n)
  Residue≃ k n
    = Residue+k k n
    , isoToIsEquiv (iso (Residue+k k n) (Residue-k k n)
                        (Residue+k-k k n) (Residue-k+k k n))

Residue≡ : ∀ k n → Residue k n ≡ Residue k (k + n)
Residue≡ k n = ua (Residue≃ k n)

-- For positive `k`, all `n` have a canonical residue mod `k`.
module Reduce (k₀ : ℕ) where
  k : ℕ
  k = suc k₀

  base : ∀ n (n<k : n < k) → Residue k n
  base n n<k = Fin→Residue (n , n<k)

  step : ∀ n → Residue k n → Residue k (k + n)
  step n = transport (Residue≡ k n)

  reduce : ∀ n → Residue k n
  reduce = +induction k₀ (Residue k) base step

  reduce≡
    : ∀ n → transport (Residue≡ k n) (reduce n) ≡ reduce (k + n)
  reduce≡ n
    = sym (+inductionStep k₀ _ base step n)

  reduceP
    : ∀ n → PathP (λ i → Residue≡ k n i) (reduce n) (reduce (k + n))
  reduceP n = toPathP (reduce≡ n)

open Reduce using (reduce; reduce≡) public

private
  lemma₅
    : ∀ k n (R : Residue k n)
    →  extract R ≡ extract (transport (Residue≡ k n) R)
  lemma₅ k n = sym ∘ cong extract ∘ uaβ (Residue≃ k n)

-- The residue of n modulo k is the same as the residue of k + n.
extract≡ : ∀ k n → extract (reduce k n) ≡ extract (reduce k (suc k + n))
extract≡ k n
  = lemma₅ (suc k) n (reduce k n) ∙ cong extract (Reduce.reduce≡ k n)

isContrResidue : ∀{k n} → isContr (Residue (suc k) n)
isContrResidue {k} {n} = inhProp→isContr (reduce k n) (isPropResidue (suc k) n)
