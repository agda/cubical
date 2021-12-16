{-# OPTIONS --safe #-}
module Cubical.Algebra.RingSolver.Solver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.RingSolver.RawAlgebra renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Algebra.RingSolver.AlgebraExpression
open import Cubical.Algebra.RingSolver.IntAsRawRing
open import Cubical.Algebra.RingSolver.HornerForms
open import Cubical.Algebra.RingSolver.EvalHom
open import Cubical.Algebra.RingSolver.HornerEval

private
  variable
    ℓ : Level

module EqualityToNormalform (R : CommRing ℓ) where
  νR = CommRing→RawℤAlgebra R
  open CommRingStr (snd R)
  open RingTheory (CommRing→Ring R)
  open Eval ℤAsRawRing νR
  open IteratedHornerOperations νR
  open HomomorphismProperties R

  ℤExpr : (n : ℕ) → Type _
  ℤExpr = Expr ℤAsRawRing (fst R)

  normalize : (n : ℕ) → ℤExpr n → IteratedHornerForms νR n
  normalize n (K r) = Constant n νR r
  normalize n (∣ k) = Variable n νR k
  normalize n (x +' y) =
    (normalize n x) +ₕ (normalize n y)
  normalize n (x ·' y) =
    (normalize n x) ·ₕ (normalize n y)
  normalize n (-' x) =  -ₕ (normalize n x)

  isEqualToNormalform :
            (n : ℕ)
            (e : ℤExpr n) (xs : Vec (fst R) n)
          → eval (normalize n e) xs ≡ ⟦ e ⟧ xs
  isEqualToNormalform ℕ.zero (K r) [] = refl
  isEqualToNormalform (ℕ.suc n) (K r) (x ∷ xs) =
     eval (Constant (ℕ.suc n) νR r) (x ∷ xs)         ≡⟨ refl ⟩
     eval (0ₕ ·X+ Constant n νR r) (x ∷ xs)           ≡⟨ combineCasesEval R 0ₕ (Constant n νR r) x xs ⟩
     eval 0ₕ (x ∷ xs) · x + eval (Constant n νR r) xs ≡⟨ cong (λ u → u · x + eval (Constant n νR r) xs)
                                                             (Eval0H (x ∷ xs)) ⟩
     0r · x + eval (Constant n νR r) xs               ≡⟨ cong
                                                          (λ u → u + eval (Constant n νR r) xs)
                                                          (0LeftAnnihilates _) ⟩
     0r + eval (Constant n νR r) xs                   ≡⟨ +Lid _ ⟩
     eval (Constant n νR r) xs                        ≡⟨ isEqualToNormalform n (K r) xs ⟩
     _ ∎

  isEqualToNormalform (ℕ.suc n) (∣ zero) (x ∷ xs) =
    eval (1ₕ ·X+ 0ₕ) (x ∷ xs)           ≡⟨ combineCasesEval R 1ₕ 0ₕ x xs ⟩
    eval 1ₕ (x ∷ xs) · x + eval 0ₕ xs   ≡⟨ cong (λ u → u · x + eval 0ₕ xs)
                                              (Eval1ₕ (x ∷ xs)) ⟩
    1r · x + eval 0ₕ xs                 ≡⟨ cong (λ u → 1r · x + u ) (Eval0H xs) ⟩
    1r · x + 0r                        ≡⟨ +Rid _ ⟩
    1r · x                             ≡⟨ ·Lid _ ⟩
    x ∎
  isEqualToNormalform (ℕ.suc n) (∣ (suc k)) (x ∷ xs) =
      eval (0ₕ ·X+ Variable n νR k) (x ∷ xs)           ≡⟨ combineCasesEval R 0ₕ (Variable n νR k) x xs ⟩
      eval 0ₕ (x ∷ xs) · x + eval (Variable n νR k) xs ≡⟨ cong (λ u → u · x + eval (Variable n νR k) xs)
                                                              (Eval0H (x ∷ xs)) ⟩
      0r · x + eval (Variable n νR k) xs              ≡⟨ cong (λ u → u + eval (Variable n νR k) xs)
                                                              (0LeftAnnihilates _) ⟩
      0r + eval (Variable n νR k) xs                  ≡⟨ +Lid _ ⟩
      eval (Variable n νR k) xs                       ≡⟨ isEqualToNormalform n (∣ k) xs ⟩
      ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

  isEqualToNormalform ℕ.zero (-' e) [] =
    eval (-ₕ (normalize ℕ.zero e)) []  ≡⟨ -EvalDist (normalize ℕ.zero e) [] ⟩
    - eval (normalize ℕ.zero e) []    ≡⟨ cong -_ (isEqualToNormalform ℕ.zero e [] ) ⟩
    - ⟦ e ⟧ [] ∎
  isEqualToNormalform (ℕ.suc n) (-' e) (x ∷ xs) =
    eval (-ₕ (normalize (ℕ.suc n) e)) (x ∷ xs) ≡⟨ -EvalDist (normalize (ℕ.suc n) e) (x ∷ xs) ⟩
    - eval (normalize (ℕ.suc n) e) (x ∷ xs)    ≡⟨ cong -_ (isEqualToNormalform (ℕ.suc n) e (x ∷ xs) ) ⟩
    - ⟦ e ⟧ (x ∷ xs) ∎

  isEqualToNormalform ℕ.zero (e +' e₁) [] =
        eval (normalize ℕ.zero e +ₕ normalize ℕ.zero e₁) []
      ≡⟨ +Homeval (normalize ℕ.zero e) _ [] ⟩
        eval (normalize ℕ.zero e) []
        + eval (normalize ℕ.zero e₁) []
      ≡⟨ cong (λ u → u + eval (normalize ℕ.zero e₁) [])
              (isEqualToNormalform ℕ.zero e []) ⟩
        ⟦ e ⟧ []
        + eval (normalize ℕ.zero e₁) []
      ≡⟨ cong (λ u → ⟦ e ⟧ [] + u) (isEqualToNormalform ℕ.zero e₁ []) ⟩
        ⟦ e ⟧ [] + ⟦ e₁ ⟧ [] ∎
  isEqualToNormalform (ℕ.suc n) (e +' e₁) (x ∷ xs) =
        eval (normalize (ℕ.suc n) e
                         +ₕ normalize (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ +Homeval (normalize (ℕ.suc n) e) _ (x ∷ xs) ⟩
        eval (normalize (ℕ.suc n) e) (x ∷ xs)
        + eval (normalize (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → u + eval (normalize (ℕ.suc n) e₁) (x ∷ xs))
              (isEqualToNormalform (ℕ.suc n) e (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs)
        + eval (normalize (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) + u)
              (isEqualToNormalform (ℕ.suc n) e₁ (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) + ⟦ e₁ ⟧ (x ∷ xs) ∎

  isEqualToNormalform ℕ.zero (e ·' e₁) [] =
        eval (normalize ℕ.zero e ·ₕ normalize ℕ.zero e₁) []
      ≡⟨ ·Homeval (normalize ℕ.zero e) _ [] ⟩
        eval (normalize ℕ.zero e) [] · eval (normalize ℕ.zero e₁) []
      ≡⟨ cong (λ u → u · eval (normalize ℕ.zero e₁) [])
              (isEqualToNormalform ℕ.zero e []) ⟩
        ⟦ e ⟧ [] · eval (normalize ℕ.zero e₁) []
      ≡⟨ cong (λ u → ⟦ e ⟧ [] · u) (isEqualToNormalform ℕ.zero e₁ []) ⟩
        ⟦ e ⟧ [] · ⟦ e₁ ⟧ [] ∎

  isEqualToNormalform (ℕ.suc n) (e ·' e₁) (x ∷ xs) =
        eval (normalize (ℕ.suc n) e
                         ·ₕ normalize (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ ·Homeval (normalize (ℕ.suc n) e) _ (x ∷ xs) ⟩
        eval (normalize (ℕ.suc n) e) (x ∷ xs)
        · eval (normalize (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → u · eval (normalize (ℕ.suc n) e₁) (x ∷ xs))
              (isEqualToNormalform (ℕ.suc n) e (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs)
        · eval (normalize (ℕ.suc n) e₁) (x ∷ xs)
      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) · u)
              (isEqualToNormalform (ℕ.suc n) e₁ (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) · ⟦ e₁ ⟧ (x ∷ xs) ∎

  solve :
    {n : ℕ} (e₁ e₂ : ℤExpr n) (xs : Vec (fst R) n)
    (p : eval (normalize n e₁) xs ≡ eval (normalize n e₂) xs)
    → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
  solve e₁ e₂ xs p =
    ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform _ e₁ xs) ⟩
    eval (normalize _ e₁) xs ≡⟨ p ⟩
    eval (normalize _ e₂) xs ≡⟨ isEqualToNormalform _ e₂ xs ⟩
    ⟦ e₂ ⟧ xs ∎

ℤExpr : (R : CommRing ℓ) (n : ℕ)
        → _
ℤExpr R n = EqualityToNormalform.ℤExpr R n

solve : (R : CommRing ℓ)
        {n : ℕ} (e₁ e₂ : ℤExpr R n) (xs : Vec (fst R) n)
        (p : eval (EqualityToNormalform.normalize R n e₁) xs ≡ eval (EqualityToNormalform.normalize R n e₂) xs)
        → _
solve R = EqualityToNormalform.solve R
