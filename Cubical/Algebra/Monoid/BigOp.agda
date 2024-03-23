{-# OPTIONS --safe #-}
module Cubical.Algebra.Monoid.BigOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData

open import Cubical.Algebra.Monoid.Base

private
  variable
    ℓ ℓ' : Level

module MonoidBigOp (M' : Monoid ℓ) where
 private M = ⟨ M' ⟩
 open MonoidStr (snd M')

 bigOp : {n : ℕ} → FinVec M n → M
 bigOp = foldrFin _·_ ε

 bigOpExt : ∀ {n} {V W : FinVec M n} → ((i : Fin n) → V i ≡ W i) → bigOp V ≡ bigOp W
 bigOpExt h = cong bigOp (funExt h)

 bigOpε : ∀ n → bigOp (replicateFinVec n ε) ≡ ε
 bigOpε zero = refl
 bigOpε (suc n) = cong (ε ·_) (bigOpε n) ∙ ·IdR _

 bigOpLast : ∀ {n} (V : FinVec M (suc n)) → bigOp V ≡ bigOp (V ∘ weakenFin) · V (fromℕ n)
 bigOpLast {n = zero} V = ·IdR _ ∙ sym (·IdL _)
 bigOpLast {n = suc n} V = cong (V zero ·_) (bigOpLast (V ∘ suc)) ∙ ·Assoc _ _ _


 -- requires a commutative monoid:
 bigOpSplit : (∀ x y → x · y ≡ y · x)
            → {n : ℕ} → (V W : FinVec M n) → bigOp (λ i → V i · W i) ≡ bigOp V · bigOp W
 bigOpSplit _ {n = zero} _ _ = sym (·IdR _)
 bigOpSplit comm {n = suc n} V W =
    V zero · W zero · bigOp (λ i → V (suc i) · W (suc i))
  ≡⟨ (λ i → V zero · W zero · bigOpSplit comm (V ∘ suc) (W ∘ suc) i) ⟩
    V zero · W zero · (bigOp (V ∘ suc) · bigOp (W ∘ suc))
  ≡⟨ sym (·Assoc _ _ _) ⟩
    V zero · (W zero · (bigOp (V ∘ suc) · bigOp (W ∘ suc)))
  ≡⟨ cong (V zero ·_) (·Assoc _ _ _) ⟩
    V zero · ((W zero · bigOp (V ∘ suc)) · bigOp (W ∘ suc))
  ≡⟨ cong (λ x → V zero · (x · bigOp (W ∘ suc))) (comm _ _) ⟩
    V zero · ((bigOp (V ∘ suc) · W zero) · bigOp (W ∘ suc))
  ≡⟨ cong (V zero ·_) (sym (·Assoc _ _ _)) ⟩
    V zero · (bigOp (V ∘ suc) · (W zero · bigOp (W ∘ suc)))
  ≡⟨ ·Assoc _ _ _ ⟩
    V zero · bigOp (V ∘ suc) · (W zero · bigOp (W ∘ suc)) ∎

 bigOpSplit++ : {n m : ℕ} → (V : FinVec M n) → (W : FinVec M m)
              → bigOp (V ++Fin W) ≡ bigOp V · bigOp W

 bigOpSplit++ {n = zero} V W = sym (·IdL _)
 bigOpSplit++ {n = suc n} V W = cong (V zero ·_) (bigOpSplit++ (V ∘ suc) W) ∙ ·Assoc _ _ _


module BigOpMap {M : Monoid ℓ} {M' : Monoid ℓ'} (φ : MonoidHom M M') where
  private module M = MonoidBigOp M
  private module M' = MonoidBigOp M'
  open IsMonoidHom (φ .snd)
  open MonoidStr ⦃...⦄
  private instance
    _ = M .snd
    _ = M' .snd

  presBigOp : {n : ℕ} (U : FinVec ⟨ M ⟩ n) → φ .fst (M.bigOp U) ≡ M'.bigOp (φ .fst ∘ U)
  presBigOp {n = zero} U = presε
  presBigOp {n = suc n} U = pres· _ _ ∙ cong (φ .fst (U zero) ·_) (presBigOp (U ∘ suc))
