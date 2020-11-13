{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.Solver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
open import Cubical.Algebra.RingSolver.AlmostRing
open import Cubical.Algebra.RingSolver.RawRing renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Algebra.RingSolver.RingExpression
open import Cubical.Algebra.RingSolver.HornerForms
open import Cubical.Algebra.RingSolver.EvaluationHomomorphism

private
  variable
    ℓ : Level

module EqualityToReification (R : AlmostRing {ℓ}) where
  νR = AlmostRing→RawRing R
  open AlmostRing R
  open Theory R
  open Eval νR
  open IteratedHornerOperations νR
  open HomomorphismProperties R

  Reify : (n : ℕ) → Expr ⟨ R ⟩ n → IteratedHornerForms νR n
  Reify n (K r) = Constant n νR r
  Reify n (∣ k) = Variable n νR k
  Reify n (x ⊕ y) =
    (Reify n x) +ₕ (Reify n y)
  Reify n (x ⊗ y) =
    (Reify n x) ·ₕ (Reify n y)
  Reify n (⊝ x) =  -ₕ (Reify n x)

  IsEqualToReification :
            (n : ℕ)
            (e : Expr ⟨ R ⟩ n) (xs : Vec ⟨ R ⟩ n)
          → Eval n (Reify n e) xs ≡ ⟦ e ⟧ xs
  IsEqualToReification ℕ.zero (K r) [] = refl
  IsEqualToReification (ℕ.suc n) (K r) (x ∷ xs) =
     Eval (ℕ.suc n) (Constant (ℕ.suc n) νR r) (x ∷ xs)           ≡⟨ refl ⟩
     Eval (ℕ.suc n) (0ₕ ·X+ Constant n νR r) (x ∷ xs)             ≡⟨ refl ⟩
     Eval (ℕ.suc n) 0ₕ (x ∷ xs) · x + Eval n (Constant n νR r) xs
    ≡⟨ cong (λ u → u · x + Eval n (Constant n νR r) xs) (Eval0H _ (x ∷ xs)) ⟩
     0r · x + Eval n (Constant n νR r) xs
    ≡⟨ cong (λ u → u + Eval n (Constant n νR r) xs) (0LeftAnnihilates _) ⟩
     0r + Eval n (Constant n νR r) xs                             ≡⟨ +Lid _ ⟩
     Eval n (Constant n νR r) xs
    ≡⟨ IsEqualToReification n (K r) xs ⟩
     r ∎

  IsEqualToReification (ℕ.suc n) (∣ zero) (x ∷ xs) =
    Eval (ℕ.suc n) (1ₕ ·X+ 0ₕ) (x ∷ xs)           ≡⟨ refl ⟩
    Eval (ℕ.suc n) 1ₕ (x ∷ xs) · x + Eval n 0ₕ xs ≡⟨ cong (λ u → u · x + Eval n 0ₕ xs)
                                                          (Eval1ₕ _ (x ∷ xs)) ⟩
    1r · x + Eval n 0ₕ xs                         ≡⟨ cong (λ u → 1r · x + u ) (Eval0H _ xs) ⟩
    1r · x + 0r                                   ≡⟨ +Rid _ ⟩
    1r · x                                        ≡⟨ ·Lid _ ⟩
    x ∎
  IsEqualToReification (ℕ.suc n) (∣ (suc k)) (x ∷ xs) =
      Eval (ℕ.suc n) (0ₕ ·X+ Variable n νR k) (x ∷ xs)             ≡⟨ refl ⟩
      Eval (ℕ.suc n) 0ₕ (x ∷ xs) · x + Eval n (Variable n νR k) xs
    ≡⟨ cong (λ u → u · x + Eval n (Variable n νR k) xs) (Eval0H _ (x ∷ xs)) ⟩
      0r · x + Eval n (Variable n νR k) xs
    ≡⟨ cong (λ u → u + Eval n (Variable n νR k) xs) (0LeftAnnihilates _) ⟩
      0r + Eval n (Variable n νR k) xs                             ≡⟨ +Lid _ ⟩
      Eval n (Variable n νR k) xs
    ≡⟨ IsEqualToReification n (∣ k) xs ⟩
      ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

  IsEqualToReification ℕ.zero (⊝ e) [] =
    Eval ℕ.zero (-ₕ (Reify ℕ.zero e)) [] ≡⟨ -EvalDist ℕ.zero
                                                                  (Reify ℕ.zero e)
                                                                  [] ⟩
    - Eval ℕ.zero (Reify ℕ.zero e) []    ≡⟨ cong -_
                                                          (IsEqualToReification
                                                            ℕ.zero e [] ) ⟩
    - ⟦ e ⟧ [] ∎
  IsEqualToReification (ℕ.suc n) (⊝ e) (x ∷ xs) =
    Eval (ℕ.suc n) (-ₕ (Reify (ℕ.suc n) e)) (x ∷ xs) ≡⟨ -EvalDist (ℕ.suc n)
                                                                  (Reify
                                                                    (ℕ.suc n) e)
                                                                  (x ∷ xs) ⟩
    - Eval (ℕ.suc n) (Reify (ℕ.suc n) e) (x ∷ xs)    ≡⟨ cong -_
                                                          (IsEqualToReification
                                                            (ℕ.suc n) e (x ∷ xs) ) ⟩
    - ⟦ e ⟧ (x ∷ xs) ∎

  IsEqualToReification ℕ.zero (e ⊕ e₁) [] =
        Eval ℕ.zero (Reify ℕ.zero e +ₕ Reify ℕ.zero e₁) []
      ≡⟨ +HomEval ℕ.zero (Reify ℕ.zero e) _ [] ⟩
        Eval ℕ.zero (Reify ℕ.zero e) []
        + Eval ℕ.zero (Reify ℕ.zero e₁) []
      ≡⟨ cong (λ u → u + Eval ℕ.zero (Reify ℕ.zero e₁) [])
              (IsEqualToReification ℕ.zero e []) ⟩
        ⟦ e ⟧ []
        + Eval ℕ.zero (Reify ℕ.zero e₁) []
      ≡⟨ cong (λ u → ⟦ e ⟧ [] + u) (IsEqualToReification ℕ.zero e₁ []) ⟩
        ⟦ e ⟧ [] + ⟦ e₁ ⟧ [] ∎
  IsEqualToReification (ℕ.suc n) (e ⊕ e₁) (x ∷ xs) =
        Eval (ℕ.suc n) (Reify (ℕ.suc n) e
                         +ₕ Reify (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ +HomEval (ℕ.suc n) (Reify (ℕ.suc n) e) _ (x ∷ xs) ⟩
        Eval (ℕ.suc n) (Reify (ℕ.suc n) e) (x ∷ xs)
        + Eval (ℕ.suc n) (Reify (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → u + Eval (ℕ.suc n) (Reify (ℕ.suc n) e₁) (x ∷ xs))
              (IsEqualToReification (ℕ.suc n) e (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs)
        + Eval (ℕ.suc n) (Reify (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) + u)
              (IsEqualToReification (ℕ.suc n) e₁ (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) + ⟦ e₁ ⟧ (x ∷ xs) ∎

  IsEqualToReification ℕ.zero (e ⊗ e₁) [] =
        Eval ℕ.zero (Reify ℕ.zero e ·ₕ Reify ℕ.zero e₁) []
      ≡⟨ ·HomEval ℕ.zero (Reify ℕ.zero e) _ [] ⟩
        Eval ℕ.zero (Reify ℕ.zero e) []
        · Eval ℕ.zero (Reify ℕ.zero e₁) []
      ≡⟨ cong (λ u → u · Eval ℕ.zero (Reify ℕ.zero e₁) [])
              (IsEqualToReification ℕ.zero e []) ⟩
        ⟦ e ⟧ []
        · Eval ℕ.zero (Reify ℕ.zero e₁) []
      ≡⟨ cong (λ u → ⟦ e ⟧ [] · u) (IsEqualToReification ℕ.zero e₁ []) ⟩
        ⟦ e ⟧ [] · ⟦ e₁ ⟧ [] ∎

  IsEqualToReification (ℕ.suc n) (e ⊗ e₁) (x ∷ xs) =
        Eval (ℕ.suc n) (Reify (ℕ.suc n) e
                         ·ₕ Reify (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ ·HomEval (ℕ.suc n) (Reify (ℕ.suc n) e) _ (x ∷ xs) ⟩
        Eval (ℕ.suc n) (Reify (ℕ.suc n) e) (x ∷ xs)
        · Eval (ℕ.suc n) (Reify (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → u · Eval (ℕ.suc n) (Reify (ℕ.suc n) e₁) (x ∷ xs))
              (IsEqualToReification (ℕ.suc n) e (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs)
        · Eval (ℕ.suc n) (Reify (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) · u)
              (IsEqualToReification (ℕ.suc n) e₁ (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) · ⟦ e₁ ⟧ (x ∷ xs) ∎

  SolveExplicit :
    (n : ℕ) (e₁ e₂ : Expr ⟨ R ⟩ n) (xs : Vec ⟨ R ⟩ n)
    (p : Eval n (Reify n e₁) xs ≡ Eval n (Reify n e₂) xs)
    → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
  SolveExplicit n e₁ e₂ xs p =
    ⟦ e₁ ⟧ xs                          ≡⟨ sym (IsEqualToReification n e₁ xs) ⟩
    Eval n (Reify n e₁) xs ≡⟨ p ⟩
    Eval n (Reify n e₂) xs ≡⟨ IsEqualToReification n e₂ xs ⟩
    ⟦ e₂ ⟧ xs ∎
