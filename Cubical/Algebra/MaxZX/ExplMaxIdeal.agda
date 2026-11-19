{-# OPTIONS --cubical #-}

module Cubical.Algebra.MaxZX.ExplMaxIdeal where

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Algebra.Matrix
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                       ; +-comm to +ℕ-comm
                                       ; +-assoc to +ℕ-assoc
                                       ; ·-assoc to ·ℕ-assoc)
open import Cubical.Data.Vec.Base using (_∷_; [])
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order using (_<'Fin_; _≤'Fin_)
open import Cubical.Data.Sum
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Base
open import Cubical.Data.Nat.Order
open import Cubical.Tactics.CommRingSolver
-- open import Cubical.Algebra.CommRing.Ideal.Base
open import Cubical.Foundations.Powerset

module ExplMaxIdeal (ℓ : Level) (P' : CommRing ℓ) where

  R' = CommRing→Ring P'

  open RingStr (snd (CommRing→Ring P')) renaming ( is-set to isSetR)
  -- open CommIdeal P'


  ∑ = Sum.∑ (CommRing→Ring P')
  ∏ = Product.∏ (CommRing→Ring P')

  R : Type ℓ
  R = ⟨ P' ⟩

  record Inspect {A : Set} (x : A) : Set where
    constructor what
    field
      it : A
      it-eq : x ≡ it

  inspect : ∀ {A : Set} (x : A) → Inspect x
  inspect x = what x refl

  smalllemma : (a : R) → (- 1r)· a + a ≡ 0r
  smalllemma a = solve! P'

  -- witness of not beeing an maximal ideal
  data WitnessNotMaximalIdeal (M : R → Bool) (ν : R → R) : Set ℓ where
    oneIn       : M 1r ≡ true                                                → WitnessNotMaximalIdeal M ν
    zeroNotIn   : M 0r ≡ false                                               → WitnessNotMaximalIdeal M ν
    sumNotIn    : (a b : R) → M a ≡ true → M b ≡ true  → M (a + b) ≡ false   → WitnessNotMaximalIdeal M ν
    multNotIn   : (a b : R) → M b ≡ true → M (a · b) ≡ false                 → WitnessNotMaximalIdeal M ν
    notMax      : (a : R) → M a ≡ false  → M (a · ν a + (- 1r)) ≡ false      → WitnessNotMaximalIdeal M ν

  -- Lemma 4 of the Papers
  explMaxToExplPrim : {n : ℕ} → (M : R → Bool) (ν : R → R) → (a : FinVec R n) → M (∏ a) ≡ true → WitnessNotMaximalIdeal M ν ⊎ Σ (Fin n) (λ i → M (a i) ≡ true)
  explMaxToExplPrim {zero} M ν a isIn = inl (oneIn isIn)
  explMaxToExplPrim {suc n} M ν a isIn with inspect (M (a zero))
  explMaxToExplPrim {suc n} M ν a isIn | what true it-eq  = inr (zero , it-eq)
  explMaxToExplPrim {suc n} M ν a isIn | what false it-eq  with inspect (M (∏ (λ i → a (suc i))))
  explMaxToExplPrim {suc n} M ν a isIn | what false it-eq | what true it-eq₁ with explMaxToExplPrim {n} M ν (λ i → a (suc i)) it-eq₁
  explMaxToExplPrim {suc n} M ν a isIn | what false it-eq | what true it-eq₁ | inl x = inl x
  explMaxToExplPrim {suc n} M ν a isIn | what false it-eq | what true it-eq₁ | inr (fst₁ , snd₁) = inr ( suc fst₁ , snd₁ )
  explMaxToExplPrim {suc n} M ν a isIn | what false it-eq | what false it-eq₁ with inspect (M ((a zero) · ν (a zero) + (- 1r)))
  explMaxToExplPrim {suc n} M ν a isIn | what false it-eq | what false it-eq₁ | what false it-eq₂ = inl (notMax (a zero) it-eq it-eq₂)
  explMaxToExplPrim {suc n} M ν a isIn | what false it-eq | what false it-eq₁ | what true it-eq₂ with inspect (M (ν (a zero) · ∏ a))
  ... | what false it-eq₃ = inl (multNotIn (ν (a zero)) (∏ a) isIn it-eq₃)
  ... | what true it-eq₃ with inspect (M (((a zero) · ν (a zero) + (- 1r)) · ∏ (λ i → a (suc i))))
  ... | what false it-eq₄ = inl (multNotIn (∏ (λ i → a (suc i))) ((a zero) · ν (a zero) + (- 1r)) it-eq₂
    (M (∏ (λ i → a (suc i)) · (a zero · ν (a zero) + - 1r))
    ≡⟨ cong (λ a₁ → M a₁) (CommRingStr.·Comm (snd P') (∏ (λ i → a (suc i))) (a zero · ν (a zero) + - 1r)) ⟩
    M
      ((snd P' CommRingStr.· (a zero · ν (a zero) + - 1r))
       (∏ (λ i → a (suc i))))
    ≡⟨ it-eq₄ ⟩
    false
    ∎))
  ... | what true it-eq₄ with inspect (M ((- 1r) · (a zero · ν (a zero) + - 1r) · ∏ (λ i → a (suc i))))
  ... | what false it-eq₅ = inl (multNotIn (- 1r) ((a zero · ν (a zero) + - 1r) · ∏ (λ i → a (suc i))) it-eq₄
    (M (- 1r · ((a zero · ν (a zero) + - 1r) · ∏ (λ i → a (suc i))))
    ≡⟨ cong (λ a₁ → M a₁)  (·Assoc _ _ _) ⟩
    M (- 1r · (a zero · ν (a zero) + - 1r) · ∏ (λ i → a (suc i)))
    ≡⟨ it-eq₅ ⟩
    false
    ∎))
  ... | what true it-eq₅ with inspect (M ((- 1r) · (a zero · ν (a zero) + - 1r) · ∏ (λ i → a (suc i)) + ν (a zero) · ∏ a))
  ... | what false it-eq₆ = inl (sumNotIn ((- 1r) · (a zero · ν (a zero) + - 1r) · ∏ (λ i → a (suc i))) (ν (a zero) · ∏ a) it-eq₅ it-eq₃ it-eq₆)
  ... | what true it-eq₆ =
    inl
      (multNotIn
      1r
      (∏ (λ i → a (suc i)))
      (
      M (∏ (λ i → a (suc i)))
      ≡⟨ cong
        (λ a₁ → M a₁)
        (∏ (λ i → a (suc i))
        ≡⟨ sym (·IdL _) ⟩
        (1r · ∏ (λ i → a (suc i)))
        ≡⟨ cong (λ x → x ·  ∏ (λ i → a (suc i))) (solve! P') ⟩
        - 1r · - 1r · ∏ (λ i → a (suc i))
        ≡⟨ sym (·Assoc _ _ _) ⟩
        (- 1r · (- 1r · ∏ (λ i → a (suc i))))
        ≡⟨ sym (+IdR _) ⟩
        (- 1r · (- 1r · ∏ (λ i → a (suc i))) + 0r)
        ∎)
       ⟩
      M (- 1r · (- 1r · ∏ (λ i → a (suc i))) + 0r)
      ≡⟨
        cong
        (λ a₁ → M (- 1r · (- 1r · ∏ (λ i → a (suc i))) + a₁))
        (sym (smalllemma (ν (a zero) · ∏ a))) ⟩
      M
        (- 1r · (- 1r · ∏ (λ i → a (suc i))) +
         (- 1r · (ν (a zero) · ∏ a) + ν (a zero) · ∏ a))
      ≡⟨
        cong
        (λ a₁ → (M a₁))
        (+Assoc _ _ _)
       ⟩
      M
        (- 1r · (- 1r · ∏ (λ i → a (suc i))) + - 1r · (ν (a zero) · ∏ a) +
         ν (a zero) · ∏ a)
      ≡⟨ cong
        (λ a₁ → (M (a₁ + ν (a zero) · ∏ a)))
        (+Comm _ _) ⟩
      M
        (- 1r · (ν (a zero) · ∏ a) + - 1r · (- 1r · ∏ (λ i → a (suc i))) +
         ν (a zero) · ∏ a)
      ≡⟨
        cong
        (λ a₁ → M(a₁ + ν (a zero) · ∏ a))
        (sym (·DistR+ _ _ _))
       ⟩
      M
        (- 1r ·
         (ν (a zero) · ∏ a +
          - 1r · ∏ (λ i → a (suc i)))
         + ν (a zero) · ∏ a)
      ≡⟨
        cong
        (λ a₁ → M
        (- 1r ·
         (a₁ +
          - 1r · ∏ (λ i → a (suc i)))
         + ν (a zero) · ∏ a))
        (·Assoc _ _ _)
       ⟩
      M
        (- 1r ·
         (ν (a zero) · a zero · ∏ (λ i → a (suc i)) +
          - 1r · ∏ (λ i → a (suc i)))
         + ν (a zero) · ∏ a)
      ≡⟨
        cong
        (λ a₁ →  M (- 1r · a₁ + ν (a zero) · ∏ a))
        (sym (·DistL+ _ _ _))
       ⟩
      M
        (- 1r · ((ν (a zero) · a zero + - 1r) · ∏ (λ i → a (suc i))) +
         ν (a zero) · ∏ a)
      ≡⟨ cong
        (λ a₁ → M(a₁ + ν (a zero) · ∏ a)) (·Assoc _ _ _) ⟩
      M ((- 1r) · ( ν (a zero) · a zero  + - 1r) · ∏ (λ i → a (suc i)) + ν (a zero) · ∏ a)
      ≡⟨ cong (λ a₁ → M (((- 1r) · (a₁ + - 1r) · ∏ (λ i → a (suc i)) + ν (a zero) · ∏ a))) (CommRingStr.·Comm (snd P') _ _)  ⟩
      M ((- 1r) · (a zero · ν (a zero) + - 1r) · ∏ (λ i → a (suc i)) + ν (a zero) · ∏ a)
      ≡⟨ it-eq₆ ⟩
      true
      ∎)
      (M (1r · ∏ (λ i → a (suc i)))
      ≡⟨ cong (λ x → M x) (·IdL _) ⟩
      M (∏ (λ i → a (suc i)))
      ≡⟨ it-eq₁ ⟩
      false
      ∎)
      )
  
