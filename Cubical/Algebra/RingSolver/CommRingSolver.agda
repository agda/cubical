{-# OPTIONS --safe #-}
module Cubical.Algebra.RingSolver.CommRingSolver where

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
open import Cubical.Algebra.RingSolver.CommRingHornerForms
open import Cubical.Algebra.RingSolver.CommRingEvalHom

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
          → eval n (normalize n e) xs ≡ ⟦ e ⟧ xs
  isEqualToNormalform ℕ.zero (K r) [] = refl
  isEqualToNormalform (ℕ.suc n) (K r) (x ∷ xs) =
     eval (ℕ.suc n) (Constant (ℕ.suc n) νR r) (x ∷ xs)           ≡⟨ refl ⟩
     eval (ℕ.suc n) (0ₕ ·X+ Constant n νR r) (x ∷ xs)             ≡⟨ combineCasesEval 0ₕ (Constant n νR r) x xs ⟩
     eval (ℕ.suc n) 0ₕ (x ∷ xs) · x + eval n (Constant n νR r) xs
    ≡⟨ cong (λ u → u · x + eval n (Constant n νR r) xs) (Eval0H _ (x ∷ xs)) ⟩
     0r · x + eval n (Constant n νR r) xs
    ≡⟨ cong (λ u → u + eval n (Constant n νR r) xs) (0LeftAnnihilates _) ⟩
     0r + eval n (Constant n νR r) xs                             ≡⟨ +Lid _ ⟩
     eval n (Constant n νR r) xs                                  ≡⟨ isEqualToNormalform n (K r) xs ⟩
     _ ∎

  isEqualToNormalform (ℕ.suc n) (∣ zero) (x ∷ xs) =
    eval (ℕ.suc n) (1ₕ ·X+ 0ₕ) (x ∷ xs)           ≡⟨ refl ⟩
    eval (ℕ.suc n) 1ₕ (x ∷ xs) · x + eval n 0ₕ xs ≡⟨ cong (λ u → u · x + eval n 0ₕ xs)
                                                          (Eval1ₕ _ (x ∷ xs)) ⟩
    1r · x + eval n 0ₕ xs                         ≡⟨ cong (λ u → 1r · x + u ) (Eval0H _ xs) ⟩
    1r · x + 0r                                   ≡⟨ +Rid _ ⟩
    1r · x                                        ≡⟨ ·Lid _ ⟩
    x ∎
  isEqualToNormalform (ℕ.suc n) (∣ (suc k)) (x ∷ xs) =
      eval (ℕ.suc n) (0ₕ ·X+ Variable n νR k) (x ∷ xs)             ≡⟨ combineCasesEval 0ₕ (Variable n νR k) x xs ⟩
      eval (ℕ.suc n) 0ₕ (x ∷ xs) · x + eval n (Variable n νR k) xs
    ≡⟨ cong (λ u → u · x + eval n (Variable n νR k) xs) (Eval0H _ (x ∷ xs)) ⟩
      0r · x + eval n (Variable n νR k) xs
    ≡⟨ cong (λ u → u + eval n (Variable n νR k) xs) (0LeftAnnihilates _) ⟩
      0r + eval n (Variable n νR k) xs                             ≡⟨ +Lid _ ⟩
      eval n (Variable n νR k) xs
    ≡⟨ isEqualToNormalform n (∣ k) xs ⟩
      ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

  isEqualToNormalform ℕ.zero (-' e) [] =
    eval ℕ.zero (-ₕ (normalize ℕ.zero e)) [] ≡⟨ -EvalDist ℕ.zero
                                                                  (normalize ℕ.zero e)
                                                                  [] ⟩
    - eval ℕ.zero (normalize ℕ.zero e) []    ≡⟨ cong -_
                                                          (isEqualToNormalform
                                                            ℕ.zero e [] ) ⟩
    - ⟦ e ⟧ [] ∎
  isEqualToNormalform (ℕ.suc n) (-' e) (x ∷ xs) =
    eval (ℕ.suc n) (-ₕ (normalize (ℕ.suc n) e)) (x ∷ xs) ≡⟨ -EvalDist (ℕ.suc n)
                                                                  (normalize
                                                                    (ℕ.suc n) e)
                                                                  (x ∷ xs) ⟩
    - eval (ℕ.suc n) (normalize (ℕ.suc n) e) (x ∷ xs)    ≡⟨ cong -_
                                                          (isEqualToNormalform
                                                            (ℕ.suc n) e (x ∷ xs) ) ⟩
    - ⟦ e ⟧ (x ∷ xs) ∎

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
    {n : ℕ} (e₁ e₂ : ℤExpr n) (xs : Vec (fst R) n)
    (p : eval n (normalize n e₁) xs ≡ eval n (normalize n e₂) xs)
    → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
  solve e₁ e₂ xs p =
    ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform _ e₁ xs) ⟩
    eval _ (normalize _ e₁) xs ≡⟨ p ⟩
    eval _ (normalize _ e₂) xs ≡⟨ isEqualToNormalform _ e₂ xs ⟩
    ⟦ e₂ ⟧ xs ∎

ℤExpr : (R : CommRing ℓ) (n : ℕ)
        → _
ℤExpr R n = EqualityToNormalform.ℤExpr R n

solve : (R : CommRing ℓ)
        {n : ℕ} (e₁ e₂ : ℤExpr R n) (xs : Vec (fst R) n)
        (p : eval n (EqualityToNormalform.normalize R n e₁) xs ≡ eval n (EqualityToNormalform.normalize R n e₂) xs)
        → _
solve R = EqualityToNormalform.solve R

module VarNames3 (R : CommRing ℓ) where
  X1 : ℤExpr R 3
  X1 = ∣ Fin.zero

  X2 : ℤExpr R 3
  X2 = ∣ (suc Fin.zero)

  X3 : ℤExpr R 3
  X3 = ∣ (suc (suc Fin.zero))

module VarNames4 (R : CommRing ℓ) where
  X1 : ℤExpr R 4
  X1 = ∣ Fin.zero

  X2 : ℤExpr R 4
  X2 = ∣ (suc Fin.zero)

  X3 : ℤExpr R 4
  X3 = ∣ (suc (suc Fin.zero))

  X4 : ℤExpr R 4
  X4 = ∣ (suc (suc (suc Fin.zero)))

module VarNames5 (R : CommRing ℓ) where
  X1 : ℤExpr R 5
  X1 = ∣ Fin.zero

  X2 : ℤExpr R 5
  X2 = ∣ (suc Fin.zero)

  X3 : ℤExpr R 5
  X3 = ∣ (suc (suc Fin.zero))

  X4 : ℤExpr R 5
  X4 = ∣ (suc (suc (suc Fin.zero)))

  X5 : ℤExpr R 5
  X5 = ∣ (suc (suc (suc (suc Fin.zero))))

module VarNames6 (R : CommRing ℓ) where
  X1 : ℤExpr R 6
  X1 = ∣ Fin.zero

  X2 : ℤExpr R 6
  X2 = ∣ (suc Fin.zero)

  X3 : ℤExpr R 6
  X3 = ∣ (suc (suc Fin.zero))

  X4 : ℤExpr R 6
  X4 = ∣ (suc (suc (suc Fin.zero)))

  X5 : ℤExpr R 6
  X5 = ∣ (suc (suc (suc (suc Fin.zero))))

  X6 : ℤExpr R 6
  X6 = ∣ (suc (suc (suc (suc (suc Fin.zero)))))
