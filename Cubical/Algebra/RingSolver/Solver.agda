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
open import Cubical.Algebra.RingSolver.HornerNormalForm
open import Cubical.Algebra.RingSolver.IteratedHornerForms
open import Cubical.Algebra.RingSolver.EvaluationHomomorphism
open import Cubical.Algebra.RingSolver.MultivariateEvaluationHomomorphism

private
  variable
    ℓ : Level

module EqualityToNormalForm (R : AlmostRing {ℓ}) where
  open ToBaseRing R
  νR = AlmostRing→RawRing R
  open AlmostRing R
  open Theory R
  open HornerOperations νR
  open Eval νR

  Reify : Expr ⟨ R ⟩ 1 → RawHornerPolynomial νR
  Reify (K r) = 0H ·X+ r
  Reify (∣ k) = X
  Reify (x ⊕ y) = (Reify x) +H (Reify y)
  Reify (x ⊗ y) = (Reify x) ·H (Reify y)
  Reify (⊝ x) =  -H (Reify x)

  isEqualToNormalForm : (e : Expr ⟨ R ⟩ 1) (x : ⟨ R ⟩)
          → evalH (Reify e) x ≡ ⟦ e ⟧ (x ∷ [])
  isEqualToNormalForm (K r) x = 0r · x + r ≡⟨ cong (λ u → u + r) (0LeftAnnihilates x) ⟩
                      0r + r ≡⟨ +Lid r ⟩
                           r ∎
  isEqualToNormalForm (∣ zero) x = (0r · x + 1r) · x + 0r ≡⟨ +Rid _ ⟩
                          (0r · x + 1r) · x ≡⟨ cong (λ u → (u + 1r) · x)
                                                    (0LeftAnnihilates x) ⟩
                              (0r + 1r) · x ≡⟨ cong (λ u → u · x) (+Lid _) ⟩
                                     1r · x ≡⟨ ·Lid _ ⟩
                                          x ∎
  isEqualToNormalForm (⊝ e) x = evalH (-H (Reify e)) x ≡⟨ -EvalDist (Reify e) x ⟩
                  - evalH (Reify e) x ≡⟨ cong (λ u → - u) (isEqualToNormalForm e x) ⟩
                  - ⟦ e ⟧ (x ∷ []) ∎
  isEqualToNormalForm (e ⊕ e₁) x =
        evalH (Reify e +H Reify e₁) x                ≡⟨ +HomEval (Reify e) (Reify e₁) x ⟩
        (evalH (Reify e) x) + (evalH (Reify e₁) x)   ≡⟨
                                                        cong
                                                         (λ u → evalH (Reify e) x + u)
                                                         (isEqualToNormalForm e₁ x) ⟩
        (evalH (Reify e) x) + (⟦ e₁ ⟧ (x ∷ []))      ≡⟨ cong
                                                          (λ u → u + ⟦ e₁ ⟧ (x ∷ []))
                                                          (isEqualToNormalForm e x) ⟩
        (⟦ e ⟧ (x ∷ [])) + (⟦ e₁ ⟧ (x ∷ [])) ∎
  isEqualToNormalForm (e ⊗ e₁) x =
    evalH (Reify e ·H Reify e₁) x          ≡⟨ ·HomEval (Reify e) (Reify e₁) x ⟩
    evalH (Reify e) x · evalH (Reify e₁) x ≡⟨ cong (λ u → evalH (Reify e) x · u)
                                                   (isEqualToNormalForm  e₁ x) ⟩
    evalH (Reify e) x · ⟦ e₁ ⟧ (x ∷ [])    ≡⟨ cong (λ u → u · ⟦ e₁ ⟧ (x ∷ []))
                                                   (isEqualToNormalForm e x) ⟩
    ⟦ e ⟧ (x ∷ []) · ⟦ e₁ ⟧ (x ∷ []) ∎

module MultivariateReification (R : AlmostRing {ℓ}) where
  νR = AlmostRing→RawRing R
  open AlmostRing R
  open Theory R
  open Eval νR
  open IteratedHornerOperations νR
  open HomomorphismProperties R

  ReifyMultivariate : (n : ℕ) → Expr ⟨ R ⟩ n → IteratedHornerForms νR n
  ReifyMultivariate n (K r) = Constant n νR r
  ReifyMultivariate n (∣ k) = Variable n νR k
  ReifyMultivariate n (x ⊕ y) =
    (ReifyMultivariate n x) +ₕ (ReifyMultivariate n y)
  ReifyMultivariate n (x ⊗ y) =
    (ReifyMultivariate n x) ·ₕ (ReifyMultivariate n y)
  ReifyMultivariate n (⊝ x) =  -ₕ (ReifyMultivariate n x)

  IsEqualToMultivariateNormalForm :
            (n : ℕ)
            (e : Expr ⟨ R ⟩ n) (xs : Vec ⟨ R ⟩ n)
          → Eval n (ReifyMultivariate n e) xs ≡ ⟦ e ⟧ xs
  IsEqualToMultivariateNormalForm ℕ.zero (K r) [] = refl
  IsEqualToMultivariateNormalForm (ℕ.suc n) (K r) (x ∷ xs) =
     Eval (ℕ.suc n) (Constant (ℕ.suc n) νR r) (x ∷ xs)           ≡⟨ refl ⟩
     Eval (ℕ.suc n) (0ₕ ·X+ Constant n νR r) (x ∷ xs)             ≡⟨ refl ⟩
     Eval (ℕ.suc n) 0ₕ (x ∷ xs) · x + Eval n (Constant n νR r) xs
    ≡⟨ cong (λ u → u · x + Eval n (Constant n νR r) xs) (Eval0H _ (x ∷ xs)) ⟩
     0r · x + Eval n (Constant n νR r) xs
    ≡⟨ cong (λ u → u + Eval n (Constant n νR r) xs) (0LeftAnnihilates _) ⟩
     0r + Eval n (Constant n νR r) xs                             ≡⟨ +Lid _ ⟩
     Eval n (Constant n νR r) xs
    ≡⟨ IsEqualToMultivariateNormalForm n (K r) xs ⟩
     r ∎

  IsEqualToMultivariateNormalForm (ℕ.suc n) (∣ zero) (x ∷ xs) =
    Eval (ℕ.suc n) (1ₕ ·X+ 0ₕ) (x ∷ xs)           ≡⟨ refl ⟩
    Eval (ℕ.suc n) 1ₕ (x ∷ xs) · x + Eval n 0ₕ xs ≡⟨ cong (λ u → u · x + Eval n 0ₕ xs)
                                                          (Eval1ₕ _ (x ∷ xs)) ⟩
    1r · x + Eval n 0ₕ xs                         ≡⟨ cong (λ u → 1r · x + u ) (Eval0H _ xs) ⟩
    1r · x + 0r                                   ≡⟨ +Rid _ ⟩
    1r · x                                        ≡⟨ ·Lid _ ⟩
    x ∎
  IsEqualToMultivariateNormalForm (ℕ.suc n) (∣ (suc k)) (x ∷ xs) =
      Eval (ℕ.suc n) (0ₕ ·X+ Variable n νR k) (x ∷ xs)             ≡⟨ refl ⟩
      Eval (ℕ.suc n) 0ₕ (x ∷ xs) · x + Eval n (Variable n νR k) xs
    ≡⟨ cong (λ u → u · x + Eval n (Variable n νR k) xs) (Eval0H _ (x ∷ xs)) ⟩
      0r · x + Eval n (Variable n νR k) xs
    ≡⟨ cong (λ u → u + Eval n (Variable n νR k) xs) (0LeftAnnihilates _) ⟩
      0r + Eval n (Variable n νR k) xs                             ≡⟨ +Lid _ ⟩
      Eval n (Variable n νR k) xs
    ≡⟨ IsEqualToMultivariateNormalForm n (∣ k) xs ⟩
      ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

  IsEqualToMultivariateNormalForm ℕ.zero (⊝ e) [] =
    Eval ℕ.zero (-ₕ (ReifyMultivariate ℕ.zero e)) [] ≡⟨ -EvalDist ℕ.zero
                                                                  (ReifyMultivariate ℕ.zero e)
                                                                  [] ⟩
    - Eval ℕ.zero (ReifyMultivariate ℕ.zero e) []    ≡⟨ cong -_
                                                          (IsEqualToMultivariateNormalForm
                                                            ℕ.zero e [] ) ⟩
    - ⟦ e ⟧ [] ∎
  IsEqualToMultivariateNormalForm (ℕ.suc n) (⊝ e) (x ∷ xs) =
    Eval (ℕ.suc n) (-ₕ (ReifyMultivariate (ℕ.suc n) e)) (x ∷ xs) ≡⟨ -EvalDist (ℕ.suc n)
                                                                  (ReifyMultivariate
                                                                    (ℕ.suc n) e)
                                                                  (x ∷ xs) ⟩
    - Eval (ℕ.suc n) (ReifyMultivariate (ℕ.suc n) e) (x ∷ xs)    ≡⟨ cong -_
                                                          (IsEqualToMultivariateNormalForm
                                                            (ℕ.suc n) e (x ∷ xs) ) ⟩
    - ⟦ e ⟧ (x ∷ xs) ∎

  IsEqualToMultivariateNormalForm ℕ.zero (e ⊕ e₁) [] =
        Eval ℕ.zero (ReifyMultivariate ℕ.zero e +ₕ ReifyMultivariate ℕ.zero e₁) []
      ≡⟨ +HomEval ℕ.zero (ReifyMultivariate ℕ.zero e) _ [] ⟩
        Eval ℕ.zero (ReifyMultivariate ℕ.zero e) []
        + Eval ℕ.zero (ReifyMultivariate ℕ.zero e₁) []
      ≡⟨ cong (λ u → u + Eval ℕ.zero (ReifyMultivariate ℕ.zero e₁) [])
              (IsEqualToMultivariateNormalForm ℕ.zero e []) ⟩
        ⟦ e ⟧ []
        + Eval ℕ.zero (ReifyMultivariate ℕ.zero e₁) []
      ≡⟨ cong (λ u → ⟦ e ⟧ [] + u) (IsEqualToMultivariateNormalForm ℕ.zero e₁ []) ⟩
        ⟦ e ⟧ [] + ⟦ e₁ ⟧ [] ∎
  IsEqualToMultivariateNormalForm (ℕ.suc n) (e ⊕ e₁) (x ∷ xs) =
        Eval (ℕ.suc n) (ReifyMultivariate (ℕ.suc n) e
                         +ₕ ReifyMultivariate (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ +HomEval (ℕ.suc n) (ReifyMultivariate (ℕ.suc n) e) _ (x ∷ xs) ⟩
        Eval (ℕ.suc n) (ReifyMultivariate (ℕ.suc n) e) (x ∷ xs)
        + Eval (ℕ.suc n) (ReifyMultivariate (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → u + Eval (ℕ.suc n) (ReifyMultivariate (ℕ.suc n) e₁) (x ∷ xs))
              (IsEqualToMultivariateNormalForm (ℕ.suc n) e (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs)
        + Eval (ℕ.suc n) (ReifyMultivariate (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) + u)
              (IsEqualToMultivariateNormalForm (ℕ.suc n) e₁ (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) + ⟦ e₁ ⟧ (x ∷ xs) ∎

  IsEqualToMultivariateNormalForm ℕ.zero (e ⊗ e₁) [] =
        Eval ℕ.zero (ReifyMultivariate ℕ.zero e ·ₕ ReifyMultivariate ℕ.zero e₁) []
      ≡⟨ ·HomEval ℕ.zero (ReifyMultivariate ℕ.zero e) _ [] ⟩
        Eval ℕ.zero (ReifyMultivariate ℕ.zero e) []
        · Eval ℕ.zero (ReifyMultivariate ℕ.zero e₁) []
      ≡⟨ cong (λ u → u · Eval ℕ.zero (ReifyMultivariate ℕ.zero e₁) [])
              (IsEqualToMultivariateNormalForm ℕ.zero e []) ⟩
        ⟦ e ⟧ []
        · Eval ℕ.zero (ReifyMultivariate ℕ.zero e₁) []
      ≡⟨ cong (λ u → ⟦ e ⟧ [] · u) (IsEqualToMultivariateNormalForm ℕ.zero e₁ []) ⟩
        ⟦ e ⟧ [] · ⟦ e₁ ⟧ [] ∎

  IsEqualToMultivariateNormalForm (ℕ.suc n) (e ⊗ e₁) (x ∷ xs) =
        Eval (ℕ.suc n) (ReifyMultivariate (ℕ.suc n) e
                         ·ₕ ReifyMultivariate (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ ·HomEval (ℕ.suc n) (ReifyMultivariate (ℕ.suc n) e) _ (x ∷ xs) ⟩
        Eval (ℕ.suc n) (ReifyMultivariate (ℕ.suc n) e) (x ∷ xs)
        · Eval (ℕ.suc n) (ReifyMultivariate (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → u · Eval (ℕ.suc n) (ReifyMultivariate (ℕ.suc n) e₁) (x ∷ xs))
              (IsEqualToMultivariateNormalForm (ℕ.suc n) e (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs)
        · Eval (ℕ.suc n) (ReifyMultivariate (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) · u)
              (IsEqualToMultivariateNormalForm (ℕ.suc n) e₁ (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) · ⟦ e₁ ⟧ (x ∷ xs) ∎

module SolverFor (R : AlmostRing {ℓ}) where
  νR = AlmostRing→RawRing R
  open HornerOperations νR
  open Eval νR

  Reify : (e : Expr ⟨ R ⟩ 1) → RawHornerPolynomial (AlmostRing→RawRing R)
  Reify e = EqualityToNormalForm.Reify R e

  isEqualToNormalForm : (e : Expr ⟨ R ⟩ 1) (x : ⟨ R ⟩)
            → evalH (Reify e) x ≡ ⟦ e ⟧ (x ∷ [])
  isEqualToNormalForm e x = EqualityToNormalForm.isEqualToNormalForm R e x

  SolveExplicit :
    (e₁ e₂ : Expr ⟨ R ⟩ 1) (x : ⟨ R ⟩)
    (p : evalH (Reify e₁) x ≡ evalH (Reify e₂) x)
    → ⟦ e₁ ⟧ (x ∷ []) ≡ ⟦ e₂ ⟧ (x ∷ [])
  SolveExplicit e₁ e₂ x p =  ⟦ e₁ ⟧ (x ∷ [])    ≡⟨ sym (isEqualToNormalForm e₁ x) ⟩
                             evalH (Reify e₁) x ≡⟨ p ⟩
                             evalH (Reify e₂) x ≡⟨ isEqualToNormalForm e₂ x ⟩
                             ⟦ e₂ ⟧ (x ∷ []) ∎
