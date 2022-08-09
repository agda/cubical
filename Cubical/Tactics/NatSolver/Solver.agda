{-# OPTIONS --safe #-}
module Cubical.Tactics.NatSolver.Solver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
open import Cubical.Tactics.NatSolver.NatExpression
open import Cubical.Tactics.NatSolver.HornerForms
open import Cubical.Tactics.NatSolver.EvalHom

private
  variable
    ℓ : Level

module EqualityToNormalform where
  open Eval
  open IteratedHornerOperations
  open HomomorphismProperties

  normalize : {n : ℕ} → Expr n → IteratedHornerForms n
  normalize {n = n} (K r) = Constant n r
  normalize {n = n} (∣ k) = Variable n k
  normalize (x +' y) =
    (normalize x) +ₕ (normalize y)
  normalize (x ·' y) =
    (normalize x) ·ₕ (normalize y)

  isEqualToNormalform :
            {n : ℕ}
            (e : Expr n) (xs : Vec ℕ n)
          → eval (normalize e) xs ≡ ⟦ e ⟧ xs
  isEqualToNormalform (K r) [] = refl
  isEqualToNormalform {n = ℕ.suc n} (K r) (x ∷ xs) =
     eval (Constant (ℕ.suc n) r) (x ∷ xs)           ≡⟨ refl ⟩
     eval (0ₕ ·X+ Constant n r) (x ∷ xs)             ≡⟨ refl ⟩
     eval 0ₕ (x ∷ xs) · x + eval (Constant n r) xs
    ≡⟨ cong (λ u → u · x + eval (Constant n r) xs) (eval0H (x ∷ xs)) ⟩
     0 · x + eval (Constant n r) xs
    ≡⟨ refl ⟩
     eval (Constant n r) xs
    ≡⟨ isEqualToNormalform (K r) xs ⟩
     r ∎

  isEqualToNormalform (∣ zero) (x ∷ xs) =
    eval (1ₕ ·X+ 0ₕ) (x ∷ xs)           ≡⟨ refl ⟩
    eval 1ₕ (x ∷ xs) · x + eval 0ₕ xs   ≡⟨ cong (λ u → u · x + eval 0ₕ xs)
                                               (eval1ₕ (x ∷ xs)) ⟩
    1 · x + eval 0ₕ xs                  ≡⟨ cong (λ u → 1 · x + u ) (eval0H xs) ⟩
    1 · x + 0                          ≡⟨ +-zero _ ⟩
    1 · x                               ≡⟨ ·-identityˡ _ ⟩
    x ∎
  isEqualToNormalform {n = ℕ.suc n} (∣ (suc k)) (x ∷ xs) =
      eval (0ₕ ·X+ Variable n k) (x ∷ xs)             ≡⟨ refl ⟩
      eval 0ₕ (x ∷ xs) · x + eval (Variable n k) xs
    ≡⟨ cong (λ u → u · x + eval (Variable n k) xs) (eval0H (x ∷ xs)) ⟩
      0 · x + eval (Variable n k) xs
    ≡⟨ refl ⟩
      eval (Variable n k) xs
    ≡⟨ isEqualToNormalform (∣ k) xs ⟩
      ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

  isEqualToNormalform (e +' e₁) [] =
        eval (normalize e +ₕ normalize e₁) []
      ≡⟨ +Homeval (normalize e) _ [] ⟩
        eval (normalize e) []
        + eval (normalize e₁) []
      ≡⟨ cong (λ u → u + eval (normalize e₁) [])
              (isEqualToNormalform e []) ⟩
        ⟦ e ⟧ []
        + eval (normalize e₁) []
      ≡⟨ cong (λ u → ⟦ e ⟧ [] + u) (isEqualToNormalform e₁ []) ⟩
        ⟦ e ⟧ [] + ⟦ e₁ ⟧ [] ∎
  isEqualToNormalform (e +' e₁) (x ∷ xs) =
        eval (normalize e
              +ₕ normalize e₁) (x ∷ xs)
      ≡⟨ +Homeval (normalize e) _ (x ∷ xs) ⟩
        eval (normalize e) (x ∷ xs)
        + eval (normalize e₁) (x ∷ xs)
      ≡⟨ cong (λ u → u + eval (normalize e₁) (x ∷ xs))
              (isEqualToNormalform e (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs)
        + eval (normalize e₁) (x ∷ xs)
      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) + u)
              (isEqualToNormalform e₁ (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) + ⟦ e₁ ⟧ (x ∷ xs) ∎

  isEqualToNormalform (e ·' e₁) [] =
        eval (normalize e ·ₕ normalize e₁) []
      ≡⟨ ·Homeval (normalize e) _ [] ⟩
        eval (normalize e) []
        · eval (normalize e₁) []
      ≡⟨ cong (λ u → u · eval (normalize e₁) [])
              (isEqualToNormalform e []) ⟩
        ⟦ e ⟧ []
        · eval (normalize e₁) []
      ≡⟨ cong (λ u → ⟦ e ⟧ [] · u) (isEqualToNormalform e₁ []) ⟩
        ⟦ e ⟧ [] · ⟦ e₁ ⟧ [] ∎

  isEqualToNormalform (e ·' e₁) (x ∷ xs) =
        eval (normalize e ·ₕ normalize e₁) (x ∷ xs)
      ≡⟨ ·Homeval (normalize e) _ (x ∷ xs) ⟩
        eval (normalize e) (x ∷ xs)
        · eval (normalize e₁) (x ∷ xs)
      ≡⟨ cong (λ u → u · eval (normalize e₁) (x ∷ xs))
              (isEqualToNormalform e (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs)
        · eval (normalize e₁) (x ∷ xs)
      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) · u)
              (isEqualToNormalform e₁ (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) · ⟦ e₁ ⟧ (x ∷ xs) ∎

  solve :
    {n : ℕ} (e₁ e₂ : Expr n) (xs : Vec ℕ n)
    (p : eval (normalize e₁) xs ≡ eval (normalize e₂) xs)
    → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
  solve e₁ e₂ xs p =
    ⟦ e₁ ⟧ xs                ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
    eval (normalize e₁) xs ≡⟨ p ⟩
    eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
    ⟦ e₂ ⟧ xs ∎
