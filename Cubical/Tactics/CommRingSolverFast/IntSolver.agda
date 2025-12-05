module Cubical.Tactics.CommRingSolverFast.IntSolver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int.Fast
open import Cubical.Algebra.Ring
open import Cubical.Tactics.CommRingSolverFast.RawAlgebra renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Tactics.CommRingSolverFast.AlgebraExpression
open import Cubical.Tactics.CommRingSolverFast.IntAsRawRing
open import Cubical.Tactics.CommRingSolverFast.HornerForms
open import Cubical.Tactics.CommRingSolverFast.EvalHomInt
open import Cubical.Tactics.CommRingSolverFast.HornerEvalInt

private
  variable
    ℓ : Level

module EqualityToNormalform where
  ℝ = ℤCommRing
  νR = ℤasRawℤAlgebra
  open CommRingStr (snd R)
  open RingTheory (CommRing→Ring R)
  open Eval ℤAsRawRing νR
  open IteratedHornerOperations νR
  open HomomorphismProperties

  ℤExpr : (n : ℕ) → Type _
  ℤExpr = Expr ℤAsRawRing (fst R)

  normalize : {n : ℕ} → ℤExpr n → IteratedHornerForms νR n
  normalize {n = n} (K r) = Constant n νR r
  normalize {n = n} (∣ k) = Variable n νR k
  normalize (x +' y) =
    (normalize x) +ₕ (normalize y)
  normalize (x ·' y) =
    (normalize x) ·ₕ (normalize y)
  normalize (-' x) =  -ₕ (normalize x)

  isEqualToNormalform :
       {n : ℕ} (e : ℤExpr n) (xs : Vec (fst R) n)
     → eval (normalize e) xs ≡ ⟦ e ⟧ xs
  isEqualToNormalform (K r) [] = refl
  isEqualToNormalform {n = ℕ.suc n} (K r) (x ∷ xs) =
     eval (Constant (ℕ.suc n) νR r) (x ∷ xs)         ≡⟨ refl ⟩
     eval (0ₕ ·X+ Constant n νR r) (x ∷ xs)           ≡⟨ combineCasesEval 0ₕ (Constant n νR r) x xs ⟩
     eval 0ₕ (x ∷ xs) · x + eval (Constant n νR r) xs ≡⟨ cong (λ u → u · x + eval (Constant n νR r) xs)
                                                             (Eval0H (x ∷ xs)) ⟩
     0r · x + eval (Constant n νR r) xs               ≡⟨ cong
                                                          (λ u → u + eval (Constant n νR r) xs)
                                                          (0LeftAnnihilates x) ⟩
     0r + eval (Constant n νR r) xs                   ≡⟨ +IdL _ ⟩
     eval (Constant n νR r) xs                        ≡⟨ isEqualToNormalform (K r) xs ⟩
     _ ∎

  isEqualToNormalform (∣ zero) (x ∷ xs) =
    eval (1ₕ ·X+ 0ₕ) (x ∷ xs)           ≡⟨ combineCasesEval 1ₕ 0ₕ x xs ⟩
    eval 1ₕ (x ∷ xs) · x + eval 0ₕ xs   ≡⟨ cong (λ u → u · x + eval 0ₕ xs)
                                              (Eval1ₕ (x ∷ xs)) ⟩
    1r · x + eval 0ₕ xs                 ≡⟨ cong (λ u → 1r · x + u ) (Eval0H xs) ⟩
    1r · x + 0r                        ≡⟨ +IdR _ ⟩
    1r · x                             ≡⟨ ·IdL _ ⟩
    x ∎
  isEqualToNormalform {n = ℕ.suc n} (∣ (suc k)) (x ∷ xs) =
      eval (0ₕ ·X+ Variable n νR k) (x ∷ xs)           ≡⟨ combineCasesEval 0ₕ (Variable n νR k) x xs ⟩
      eval 0ₕ (x ∷ xs) · x + eval (Variable n νR k) xs ≡⟨ cong (λ u → u · x + eval (Variable n νR k) xs)
                                                              (Eval0H (x ∷ xs)) ⟩
      0r · x + eval (Variable n νR k) xs              ≡⟨ cong (λ u → u + eval (Variable n νR k) xs)
                                                              (0LeftAnnihilates x) ⟩
      0r + eval (Variable n νR k) xs                  ≡⟨ +IdL _ ⟩
      eval (Variable n νR k) xs                       ≡⟨ isEqualToNormalform (∣ k) xs ⟩
      ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

  isEqualToNormalform (-' e) [] =
    eval (-ₕ (normalize e)) []  ≡⟨ -EvalDist (normalize e) [] ⟩
    - eval (normalize e) []    ≡⟨ cong -_ (isEqualToNormalform e [] ) ⟩
    - ⟦ e ⟧ [] ∎
  isEqualToNormalform (-' e) (x ∷ xs) =
    eval (-ₕ (normalize e)) (x ∷ xs) ≡⟨ -EvalDist (normalize e) (x ∷ xs) ⟩
    - eval (normalize e) (x ∷ xs)    ≡⟨ cong -_ (isEqualToNormalform e (x ∷ xs) ) ⟩
    - ⟦ e ⟧ (x ∷ xs) ∎

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
        eval (normalize e +ₕ normalize e₁) (x ∷ xs)
      ≡⟨ +Homeval (normalize e) _ (x ∷ xs) ⟩
        eval (normalize e) (x ∷ xs) + eval (normalize e₁) (x ∷ xs)
      ≡⟨ cong (λ u → u + eval (normalize e₁) (x ∷ xs))
              (isEqualToNormalform e (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) + eval (normalize e₁) (x ∷ xs)
      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) + u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) + ⟦ e₁ ⟧ (x ∷ xs) ∎

  isEqualToNormalform (e ·' e₁) [] =
        eval (normalize e ·ₕ normalize e₁) []
      ≡⟨ ·Homeval (normalize e) _ [] ⟩
        eval (normalize e) [] · eval (normalize e₁) []
      ≡⟨ cong (λ u → u · eval (normalize e₁) [])
              (isEqualToNormalform e []) ⟩
        ⟦ e ⟧ [] · eval (normalize e₁) []
      ≡⟨ cong (λ u → ⟦ e ⟧ [] · u) (isEqualToNormalform e₁ []) ⟩
        ⟦ e ⟧ [] · ⟦ e₁ ⟧ [] ∎

  isEqualToNormalform (e ·' e₁) (x ∷ xs) =
        eval (normalize e ·ₕ normalize e₁) (x ∷ xs)
      ≡⟨ ·Homeval (normalize e) _ (x ∷ xs) ⟩
        eval (normalize e) (x ∷ xs) · eval (normalize e₁) (x ∷ xs)
      ≡⟨ cong (λ u → u · eval (normalize e₁) (x ∷ xs))
              (isEqualToNormalform e (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) · eval (normalize e₁) (x ∷ xs)
      ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) · u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
        ⟦ e ⟧ (x ∷ xs) · ⟦ e₁ ⟧ (x ∷ xs) ∎

  solve :
    {n : ℕ} (e₁ e₂ : ℤExpr n) (xs : Vec (fst R) n)
    (p : eval (normalize e₁) xs ≡ eval (normalize e₂) xs)
    → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
  solve e₁ e₂ xs p =
    ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
    eval (normalize e₁) xs ≡⟨ p ⟩
    eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
    ⟦ e₂ ⟧ xs ∎



ℤExpr : (R : CommRing ℓ) (n : ℕ)
        → _
ℤExpr R n = EqualityToNormalform.ℤExpr n

solve : {n : ℕ} (e₁ e₂ : ℤExpr R n) (xs : Vec (fst R) n)
        (p : eval (EqualityToNormalform.normalize e₁) xs ≡ eval (EqualityToNormalform.normalize e₂) xs)
        → _
solve = EqualityToNormalform.solve


normaliseRing : 
        {n : ℕ} (e₁ : ℤExpr R n) (xs : Vec (fst R) n)

        → _
normaliseRing {n} e xs  = sym (EqualityToNormalform.isEqualToNormalform e xs)
