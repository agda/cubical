{-# OPTIONS --safe #-}
module Cubical.Algebra.Semiring.BigOps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData
open import Cubical.Data.Bool using (if_then_else_)

open import Cubical.Algebra.Semiring.Base
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.BigOp

private variable
  ℓ ℓ' : Level


module KroneckerDelta (S : Semiring ℓ) where
  open SemiringStr (snd S)

  δ : {n : ℕ} (i j : Fin n) → fst S
  δ i j = if i == j then 1r else 0r


module Sum (S : Semiring ℓ) where
  open MonoidBigOp (CommMonoid→Monoid (Semiring→CommMonoid S))
  open SemiringStr (snd S)
  open KroneckerDelta S

  ∑ : {n : ℕ} → FinVec (fst S) n → (fst S)
  ∑ = bigOp

  ∑Ext = bigOpExt
  ∑0r = bigOpε
  ∑Last = bigOpLast

  ∑Split : ∀ {n} → (V W : FinVec (fst S) n) → ∑ (λ i → V i + W i) ≡ ∑ V + ∑ W
  ∑Split = bigOpSplit +Comm

  ∑Split++ : ∀ {n m : ℕ} (V : FinVec (fst S) n) (W : FinVec (fst S) m)
          → ∑ (V ++Fin W) ≡ ∑ V + ∑ W
  ∑Split++ = bigOpSplit++

  ∑Mulrdist : ∀ {n} → (x : fst S) → (V : FinVec (fst S) n)
                 → x · ∑ V ≡ ∑ λ i → x · V i
  ∑Mulrdist {n = zero}  x _ = AnnihilR x
  ∑Mulrdist {n = suc n} x V =
    x · (V zero + ∑ (V ∘ suc))           ≡⟨ ·DistR+ _ _ _ ⟩
    x · V zero + x · ∑ (V ∘ suc)         ≡⟨ (λ i → x · V zero + ∑Mulrdist x (V ∘ suc) i) ⟩
    x · V zero + ∑ (λ i → x · V (suc i)) ∎

  ∑Mulldist : ∀ {n} → (x : (fst S)) → (V : FinVec (fst S) n)
                 → (∑ V) · x ≡ ∑ λ i → V i · x
  ∑Mulldist {n = zero}  x _ = AnnihilL x
  ∑Mulldist {n = suc n} x V =
    (V zero + ∑ (V ∘ suc)) · x           ≡⟨ ·DistL+ _ _ _ ⟩
    V zero · x + (∑ (V ∘ suc)) · x       ≡⟨ (λ i → V zero · x + ∑Mulldist x (V ∘ suc) i) ⟩
    V zero · x + ∑ (λ i → V (suc i) · x) ∎

  ∑Mulr0 : ∀ {n} → (V : FinVec (fst S) n) → ∑ (λ i → V i · 0r) ≡ 0r
  ∑Mulr0 V = sym (∑Mulldist 0r V) ∙ AnnihilR _

  ∑Mul0r : ∀ {n} → (V : FinVec (fst S) n) → ∑ (λ i → 0r · V i) ≡ 0r
  ∑Mul0r V = sym (∑Mulrdist 0r V) ∙ AnnihilL _

  ∑Mulr1 : (n : ℕ) (V : FinVec (fst S) n) → (j : Fin n) → ∑ (λ i → V i · δ i j) ≡ V j
  ∑Mulr1 (suc n) V zero = (λ k → ·IdR (V zero) k + ∑Mulr0 (V ∘ suc) k) ∙ +IdR (V zero)
  ∑Mulr1 (suc n) V (suc j) =
     (λ i → AnnihilR (V zero) i + ∑ (λ x → V (suc x) · δ x j))
     ∙∙ +IdL _ ∙∙ ∑Mulr1 n (V ∘ suc) j

  ∑Mul1r : (n : ℕ) (V : FinVec (fst S) n) → (j : Fin n) → ∑ (λ i → (δ j i) · V i) ≡ V j
  ∑Mul1r (suc n) V zero = (λ k → ·IdL (V zero) k + ∑Mul0r (V ∘ suc) k) ∙ +IdR (V zero)
  ∑Mul1r (suc n) V (suc j) =
    (λ i → AnnihilL (V zero) i + ∑ (λ i → (δ j i) · V (suc i)))
    ∙∙ +IdL _ ∙∙ ∑Mul1r n (V ∘ suc) j
