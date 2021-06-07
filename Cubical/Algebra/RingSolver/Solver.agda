{-# OPTIONS --safe #-}
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

module EqualityToNormalform (R : AlmostRing ℓ) where
  νR = AlmostRing→RawRing R
  open AlmostRing R
  open Theory R
  open Eval νR
  open IteratedHornerOperations νR
  open HomomorphismProperties R

  normalize : (n : ℕ) → Expr ⟨ R ⟩ n → IteratedHornerForms νR n
  normalize n (K r) = Constant n νR r
  normalize n (∣ k) = Variable n νR k
  normalize n (x ⊕ y) =
    (normalize n x) +ₕ (normalize n y)
  normalize n (x ⊗ y) =
    (normalize n x) ·ₕ (normalize n y)
  normalize n (⊝ x) =  -ₕ (normalize n x)

  isEqualToNormalform :
            (n : ℕ)
            (e : Expr ⟨ R ⟩ n) (xs : Vec ⟨ R ⟩ n)
          → eval n (normalize n e) xs ≡ ⟦ e ⟧ xs
  isEqualToNormalform ℕ.zero (K r) [] = refl
  isEqualToNormalform (ℕ.suc n) (K r) (x ∷ xs) =
     eval (ℕ.suc n) (Constant (ℕ.suc n) νR r) (x ∷ xs)           ≡⟨ refl ⟩
     eval (ℕ.suc n) (0ₕ ·X+ Constant n νR r) (x ∷ xs)             ≡⟨ refl ⟩
     eval (ℕ.suc n) 0ₕ (x ∷ xs) · x + eval n (Constant n νR r) xs
    ≡⟨ cong (λ u → u · x + eval n (Constant n νR r) xs) (eval0H _ (x ∷ xs)) ⟩
     0r · x + eval n (Constant n νR r) xs
    ≡⟨ cong (λ u → u + eval n (Constant n νR r) xs) (0LeftAnnihilates _) ⟩
     0r + eval n (Constant n νR r) xs                             ≡⟨ +Lid _ ⟩
     eval n (Constant n νR r) xs
    ≡⟨ isEqualToNormalform n (K r) xs ⟩
     r ∎

  isEqualToNormalform (ℕ.suc n) (∣ zero) (x ∷ xs) =
    eval (ℕ.suc n) (1ₕ ·X+ 0ₕ) (x ∷ xs)           ≡⟨ refl ⟩
    eval (ℕ.suc n) 1ₕ (x ∷ xs) · x + eval n 0ₕ xs ≡⟨ cong (λ u → u · x + eval n 0ₕ xs)
                                                          (eval1ₕ _ (x ∷ xs)) ⟩
    1r · x + eval n 0ₕ xs                         ≡⟨ cong (λ u → 1r · x + u ) (eval0H _ xs) ⟩
    1r · x + 0r                                   ≡⟨ +Rid _ ⟩
    1r · x                                        ≡⟨ ·Lid _ ⟩
    x ∎
  isEqualToNormalform (ℕ.suc n) (∣ (suc k)) (x ∷ xs) =
      eval (ℕ.suc n) (0ₕ ·X+ Variable n νR k) (x ∷ xs)             ≡⟨ refl ⟩
      eval (ℕ.suc n) 0ₕ (x ∷ xs) · x + eval n (Variable n νR k) xs
    ≡⟨ cong (λ u → u · x + eval n (Variable n νR k) xs) (eval0H _ (x ∷ xs)) ⟩
      0r · x + eval n (Variable n νR k) xs
    ≡⟨ cong (λ u → u + eval n (Variable n νR k) xs) (0LeftAnnihilates _) ⟩
      0r + eval n (Variable n νR k) xs                             ≡⟨ +Lid _ ⟩
      eval n (Variable n νR k) xs
    ≡⟨ isEqualToNormalform n (∣ k) xs ⟩
      ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

  isEqualToNormalform ℕ.zero (⊝ e) [] =
    eval ℕ.zero (-ₕ (normalize ℕ.zero e)) [] ≡⟨ -evalDist ℕ.zero
                                                                  (normalize ℕ.zero e)
                                                                  [] ⟩
    - eval ℕ.zero (normalize ℕ.zero e) []    ≡⟨ cong -_
                                                          (isEqualToNormalform
                                                            ℕ.zero e [] ) ⟩
    - ⟦ e ⟧ [] ∎
  isEqualToNormalform (ℕ.suc n) (⊝ e) (x ∷ xs) =
    eval (ℕ.suc n) (-ₕ (normalize (ℕ.suc n) e)) (x ∷ xs) ≡⟨ -evalDist (ℕ.suc n)
                                                                  (normalize
                                                                    (ℕ.suc n) e)
                                                                  (x ∷ xs) ⟩
    - eval (ℕ.suc n) (normalize (ℕ.suc n) e) (x ∷ xs)    ≡⟨ cong -_
                                                          (isEqualToNormalform
                                                            (ℕ.suc n) e (x ∷ xs) ) ⟩
    - ⟦ e ⟧ (x ∷ xs) ∎

  isEqualToNormalform ℕ.zero (e ⊕ e₁) [] =
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
  isEqualToNormalform (ℕ.suc n) (e ⊕ e₁) (x ∷ xs) =
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

  isEqualToNormalform ℕ.zero (e ⊗ e₁) [] =
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

  isEqualToNormalform (ℕ.suc n) (e ⊗ e₁) (x ∷ xs) =
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
    {n : ℕ} (e₁ e₂ : Expr ⟨ R ⟩ n) (xs : Vec ⟨ R ⟩ n)
    (p : eval n (normalize n e₁) xs ≡ eval n (normalize n e₂) xs)
    → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
  solve e₁ e₂ xs p =
    ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform _ e₁ xs) ⟩
    eval _ (normalize _ e₁) xs ≡⟨ p ⟩
    eval _ (normalize _ e₂) xs ≡⟨ isEqualToNormalform _ e₂ xs ⟩
    ⟦ e₂ ⟧ xs ∎
