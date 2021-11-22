{-# OPTIONS --safe #-}
module Cubical.Algebra.Monoid.BigOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP

open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.FinData

open import Cubical.Algebra.Monoid.Base

private
  variable
    ℓ : Level

module MonoidBigOp (M' : Monoid ℓ) where
 private M = ⟨ M' ⟩
 open MonoidStr (snd M')

 bigOp : {n : ℕ} → FinVec M n → M
 bigOp = foldrFin _·_ ε

 bigOpExt : ∀ {n} {V W : FinVec M n} → ((i : Fin n) → V i ≡ W i) → bigOp V ≡ bigOp W
 bigOpExt h = cong bigOp (funExt h)

 bigOpε : ∀ n → bigOp (replicateFinVec n ε) ≡ ε
 bigOpε zero = refl
 bigOpε (suc n) = cong (ε ·_) (bigOpε n) ∙ rid _

 bigOpLast : ∀ {n} (V : FinVec M (suc n)) → bigOp V ≡ bigOp (V ∘ weakenFin) · V (fromℕ n)
 bigOpLast {n = zero} V = rid _ ∙ sym (lid _)
 bigOpLast {n = suc n} V = cong (V zero ·_) (bigOpLast (V ∘ suc)) ∙ assoc _ _ _


 -- requires a commutative monoid:
 bigOpSplit : (∀ x y → x · y ≡ y · x)
            → {n : ℕ} → (V W : FinVec M n) → bigOp (λ i → V i · W i) ≡ bigOp V · bigOp W
 bigOpSplit _ {n = zero} _ _ = sym (rid _)
 bigOpSplit comm {n = suc n} V W =
    V zero · W zero · bigOp (λ i → V (suc i) · W (suc i))
  ≡⟨ (λ i → V zero · W zero · bigOpSplit comm (V ∘ suc) (W ∘ suc) i) ⟩
    V zero · W zero · (bigOp (V ∘ suc) · bigOp (W ∘ suc))
  ≡⟨ sym (assoc _ _ _) ⟩
    V zero · (W zero · (bigOp (V ∘ suc) · bigOp (W ∘ suc)))
  ≡⟨ cong (V zero ·_) (assoc _ _ _) ⟩
    V zero · ((W zero · bigOp (V ∘ suc)) · bigOp (W ∘ suc))
  ≡⟨ cong (λ x → V zero · (x · bigOp (W ∘ suc))) (comm _ _) ⟩
    V zero · ((bigOp (V ∘ suc) · W zero) · bigOp (W ∘ suc))
  ≡⟨ cong (V zero ·_) (sym (assoc _ _ _)) ⟩
    V zero · (bigOp (V ∘ suc) · (W zero · bigOp (W ∘ suc)))
  ≡⟨ assoc _ _ _ ⟩
    V zero · bigOp (V ∘ suc) · (W zero · bigOp (W ∘ suc)) ∎

 bigOpSplit++ : (∀ x y → x · y ≡ y · x)
              → {n m : ℕ} → (V : FinVec M n) → (W : FinVec M m)
              → bigOp (V ++Fin W) ≡ bigOp V · bigOp W
 bigOpSplit++ comm {n = zero} V W = sym (lid _)
 bigOpSplit++ comm {n = suc n} V W = cong (V zero ·_) (bigOpSplit++ comm (V ∘ suc) W) ∙ assoc _ _ _
