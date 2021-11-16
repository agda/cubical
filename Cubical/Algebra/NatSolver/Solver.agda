{-# OPTIONS --safe #-}
module Cubical.Algebra.NatSolver.Solver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
open import Cubical.Algebra.NatSolver.NatExpression
open import Cubical.Algebra.NatSolver.HornerForms
open import Cubical.Algebra.NatSolver.EvaluationHomomorphism

private
  variable
    ℓ : Level

module EqualityToNormalform where
  open Eval
  open IteratedHornerOperations
  open HomomorphismProperties

  normalize : (n : ℕ) → Expr n → IteratedHornerForms n
  normalize n (K r) = Constant n r
  normalize n (∣ k) = Variable n k
  normalize n (x +' y) =
    (normalize n x) +ₕ (normalize n y)
  normalize n (x ·' y) =
    (normalize n x) ·ₕ (normalize n y)

  isEqualToNormalform :
            (n : ℕ)
            (e : Expr n) (xs : Vec ℕ n)
          → eval n (normalize n e) xs ≡ ⟦ e ⟧ xs
  isEqualToNormalform ℕ.zero (K r) [] = refl
  isEqualToNormalform (ℕ.suc n) (K r) (x ∷ xs) =
     eval (ℕ.suc n) (Constant (ℕ.suc n) r) (x ∷ xs)           ≡⟨ refl ⟩
     eval (ℕ.suc n) (0ₕ ·X+ Constant n r) (x ∷ xs)             ≡⟨ refl ⟩
     eval (ℕ.suc n) 0ₕ (x ∷ xs) · x + eval n (Constant n r) xs
    ≡⟨ cong (λ u → u · x + eval n (Constant n r) xs) (eval0H _ (x ∷ xs)) ⟩
     0 · x + eval n (Constant n r) xs
    ≡⟨ refl ⟩
     eval n (Constant n r) xs
    ≡⟨ isEqualToNormalform n (K r) xs ⟩
     r ∎

  isEqualToNormalform (ℕ.suc n) (∣ zero) (x ∷ xs) =
    eval (ℕ.suc n) (1ₕ ·X+ 0ₕ) (x ∷ xs)           ≡⟨ refl ⟩
    eval (ℕ.suc n) 1ₕ (x ∷ xs) · x + eval n 0ₕ xs ≡⟨ cong (λ u → u · x + eval n 0ₕ xs)
                                                          (eval1ₕ _ (x ∷ xs)) ⟩
    1 · x + eval n 0ₕ xs                         ≡⟨ cong (λ u → 1 · x + u ) (eval0H _ xs) ⟩
    1 · x + 0                                   ≡⟨ +-zero _ ⟩
    1 · x                                        ≡⟨ ·-identityˡ _ ⟩
    x ∎
  isEqualToNormalform (ℕ.suc n) (∣ (suc k)) (x ∷ xs) =
      eval (ℕ.suc n) (0ₕ ·X+ Variable n k) (x ∷ xs)             ≡⟨ refl ⟩
      eval (ℕ.suc n) 0ₕ (x ∷ xs) · x + eval n (Variable n k) xs
    ≡⟨ cong (λ u → u · x + eval n (Variable n k) xs) (eval0H _ (x ∷ xs)) ⟩
      0 · x + eval n (Variable n k) xs
    ≡⟨ refl ⟩
      eval n (Variable n k) xs
    ≡⟨ isEqualToNormalform n (∣ k) xs ⟩
      ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

  isEqualToNormalform ℕ.zero (e +' e₁) [] =
        eval ℕ.zero (normalize ℕ.zero e +ₕ normalize ℕ.zero e₁) []
      ≡⟨ +Homeval ℕ.zero (normalize ℕ.zero e) _ [] ⟩
        eval ℕ.zero (normalize ℕ.zero e) []
        + eval ℕ.zero (normalize ℕ.zero e₁) []
      ≡⟨ cong (λ u → u + eval ℕ.zero (normalize ℕ.zero e₁) [])
              (isEqualToNormalform ℕ.zero e []) ⟩
        ⟦ e ⟧ []
        + eval ℕ.zero (normalize ℕ.zero e₁) []
      ≡⟨ cong (λ u → ⟦ e ⟧ [] + u) (isEqualToNormalform ℕ.zero e₁ []) ⟩
        ⟦ e ⟧ [] + ⟦ e₁ ⟧ [] ∎
  isEqualToNormalform (ℕ.suc n) (e +' e₁) (x ∷ xs) =
        eval (ℕ.suc n) (normalize (ℕ.suc n) e
                         +ₕ normalize (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ +Homeval (ℕ.suc n) (normalize (ℕ.suc n) e) _ (x ∷ xs) ⟩
        eval (ℕ.suc n) (normalize (ℕ.suc n) e) (x ∷ xs)
        + eval (ℕ.suc n) (normalize (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → u + eval (ℕ.suc n) (normalize (ℕ.suc n) e₁) (x ∷ xs))
              (isEqualToNormalform (ℕ.suc n) e (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs)
        + eval (ℕ.suc n) (normalize (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) + u)
              (isEqualToNormalform (ℕ.suc n) e₁ (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) + ⟦ e₁ ⟧ (x ∷ xs) ∎

  isEqualToNormalform ℕ.zero (e ·' e₁) [] =
        eval ℕ.zero (normalize ℕ.zero e ·ₕ normalize ℕ.zero e₁) []
      ≡⟨ ·Homeval ℕ.zero (normalize ℕ.zero e) _ [] ⟩
        eval ℕ.zero (normalize ℕ.zero e) []
        · eval ℕ.zero (normalize ℕ.zero e₁) []
      ≡⟨ cong (λ u → u · eval ℕ.zero (normalize ℕ.zero e₁) [])
              (isEqualToNormalform ℕ.zero e []) ⟩
        ⟦ e ⟧ []
        · eval ℕ.zero (normalize ℕ.zero e₁) []
      ≡⟨ cong (λ u → ⟦ e ⟧ [] · u) (isEqualToNormalform ℕ.zero e₁ []) ⟩
        ⟦ e ⟧ [] · ⟦ e₁ ⟧ [] ∎

  isEqualToNormalform (ℕ.suc n) (e ·' e₁) (x ∷ xs) =
        eval (ℕ.suc n) (normalize (ℕ.suc n) e
                         ·ₕ normalize (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ ·Homeval (ℕ.suc n) (normalize (ℕ.suc n) e) _ (x ∷ xs) ⟩
        eval (ℕ.suc n) (normalize (ℕ.suc n) e) (x ∷ xs)
        · eval (ℕ.suc n) (normalize (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → u · eval (ℕ.suc n) (normalize (ℕ.suc n) e₁) (x ∷ xs))
              (isEqualToNormalform (ℕ.suc n) e (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs)
        · eval (ℕ.suc n) (normalize (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) · u)
              (isEqualToNormalform (ℕ.suc n) e₁ (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) · ⟦ e₁ ⟧ (x ∷ xs) ∎

  solve :
    {n : ℕ} (e₁ e₂ : Expr n) (xs : Vec ℕ n)
    (p : eval n (normalize n e₁) xs ≡ eval n (normalize n e₂) xs)
    → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
  solve e₁ e₂ xs p =
    ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform _ e₁ xs) ⟩
    eval _ (normalize _ e₁) xs ≡⟨ p ⟩
    eval _ (normalize _ e₂) xs ≡⟨ isEqualToNormalform _ e₂ xs ⟩
    ⟦ e₂ ⟧ xs ∎
