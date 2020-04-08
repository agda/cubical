{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Connected.FreudenthalProof.7-5-14 where

open import Cubical.HITs.Truncation.Connected.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Nat hiding (elim)
open import Cubical.HITs.Nullification hiding (elim)
open import Cubical.HITs.Truncation.Base
open import Cubical.HITs.Truncation.Properties

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'


Lemma7-5-14 : (n : ℕ₋₂) (f : A → B) → (is- n -Connected f) → ∥ A ∥ n ≃ ∥ B ∥ n
Lemma7-5-14 {A = A} {B = B} neg2 f c = isoToEquiv (iso (λ _ → fst (isOfHLevelTrunc 0))
                                                       (λ _ → fst (isOfHLevelTrunc 0))
                                                       (λ b → snd (isOfHLevelTrunc 0) b)
                                                       (λ b → snd (isOfHLevelTrunc 0) b))
Lemma7-5-14 {A = A} {B = B} (-1+ n) f c = isoToEquiv (iso
                                          (∥ f ∥-fun (-1+ n))
                                          (elim (λ _ → isOfHLevelTrunc (suc n)) back)
                                          (elim (λ x → (isOfHLevelSuc (suc n) (isOfHLevelTrunc (suc n))) _ _) backSection)
                                          (elim (λ x → (isOfHLevelSuc (suc n) (isOfHLevelTrunc (suc n))) _ _) backRetract))
  where
  back :  B → ∥ A ∥ (-1+ n)
  back  y = ∥ fst ∥-fun (-1+ n) (fst (c y))

  backSection :  (b : B) → _≡_ {A = ∥ B ∥ (-1+ n)}
                               (elim (λ _ → isOfHLevelTrunc (suc n)) (λ a → ∣ f a ∣) (elim {n = suc n }
                                                                                     {B = λ _ → ∥ A ∥ (-1+ n)} (λ _ → isOfHLevelTrunc (suc n)) back ∣ b ∣))
                               ∣ b ∣
  backSection b = helper {P = λ p → ∥ f ∥-fun (-1+ n) p ≡ ∣ b ∣}
                         (λ x → (isOfHLevelSuc (suc n) (isOfHLevelTrunc (suc n)))
                           (∥ f ∥-fun (-1+ n) (∥ fst ∥-fun (-1+ n) x)) ∣ b ∣)
                         (λ a p → cong (λ x → ∣ x ∣) p)
                         (fst (c b))

    where
    helper : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {P : ∥ A ∥ (-1+ n) → Type ℓ''} →
             ((x : ∥ Σ A B ∥ (-2+ ℕ₋₂.n (-1+ n))) →
             isOfHLevel (2+ (-2+ ℕ₋₂.n (-1+ n))) (P (∥ fst ∥-fun (-1+ n) x))) →
             ((a : A) (b : B a) → P ∣ a ∣) →
             (p : ∥ Σ A B ∥ (-1+ n)) →  P (∥ fst ∥-fun (-1+ n) p)
    helper hlev pf = elim hlev λ pair → pf (fst pair) (snd pair)

  backRetract : (a : A) → ∥ fst ∥-fun (-1+ n) (fst (c (f a))) ≡ ∣ a ∣
  backRetract a = cong (∥ fst ∥-fun (-1+ n))
                       (snd (c (f a)) ∣ a , refl ∣)
