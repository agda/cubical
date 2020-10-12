{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.Solver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
open import Cubical.Algebra.RingSolver.AlmostRing
open import Cubical.Algebra.RingSolver.RawRing renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Algebra.RingSolver.HornerNormalForm
open import Cubical.Algebra.RingSolver.MultivariatePolynomials
open import Cubical.Algebra.RingSolver.RingExpression
open import Cubical.Algebra.RingSolver.EvaluationHomomorphism

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
  open ToBaseRing R
  νR = AlmostRing→RawRing R
  open AlmostRing R
  open Theory R
  open Eval νR

  ReifyMultivariate : (n : ℕ) → Expr ⟨ R ⟩ n → ⟨ IteratedHornerForms n νR ⟩ᵣ
  ReifyMultivariate n (K r) = Constant n νR r
  ReifyMultivariate n (∣ k) = Variable n νR k
  ReifyMultivariate (ℕ.suc n) (x ⊕ y) =
    (ReifyMultivariate (ℕ.suc n) x) +H (ReifyMultivariate (ℕ.suc n) y)
    where
      _+H_ : ⟨ IteratedHornerForms (ℕ.suc n) νR ⟩ᵣ → ⟨ IteratedHornerForms (ℕ.suc n) νR ⟩ᵣ → _
      x +H y = HornerOperations._+H_ (IteratedHornerForms n νR) x y
  ReifyMultivariate (ℕ.suc n) (x ⊗ y) =
    (ReifyMultivariate (ℕ.suc n) x) ·H (ReifyMultivariate (ℕ.suc n) y)
    where
      _·H_ : ⟨ IteratedHornerForms (ℕ.suc n) νR ⟩ᵣ → ⟨ IteratedHornerForms (ℕ.suc n) νR ⟩ᵣ → _
      x ·H y = HornerOperations._·H_ (IteratedHornerForms n νR) x y
  ReifyMultivariate (ℕ.suc n) (⊝ x) =  -H (ReifyMultivariate (ℕ.suc n) x)
    where
      -H_ : ⟨ IteratedHornerForms (ℕ.suc n) νR ⟩ᵣ → _
      -H x = HornerOperations.-H_ (IteratedHornerForms n νR) x
  ReifyMultivariate ℕ.zero (x ⊕ y) = ReifyMultivariate ℕ.zero x + ReifyMultivariate ℕ.zero y
  ReifyMultivariate ℕ.zero (x ⊗ y) = ReifyMultivariate ℕ.zero x · ReifyMultivariate ℕ.zero y
  ReifyMultivariate ℕ.zero (⊝ x) =  - ReifyMultivariate ℕ.zero x

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
