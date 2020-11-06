{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.EvaluationHomomorphism where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base

open import Cubical.Algebra.RingSolver.AlmostRing
open import Cubical.Algebra.RingSolver.RawRing renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Algebra.RingSolver.HornerNormalForm
open import Cubical.Algebra.RingSolver.IteratedHornerForms
open import Cubical.Algebra.RingSolver.RingExpression

private
  variable
    ℓ : Level

module ToBaseRing (R : AlmostRing {ℓ}) where
  private
    νR = AlmostRing→RawRing R
  open AlmostRing R
  open Theory R
  open HornerOperations νR
  open Eval νR

  -EvalDist :
    (P : RawHornerPolynomial νR) (x : ⟨ R ⟩)
    → evalH (-H P) x ≡ - evalH P x
  -EvalDist 0H x = 0r ≡⟨ sym 0IsSelfinverse ⟩ - 0r ∎
  -EvalDist (P ·X+ r) x =
         evalH (-H (P ·X+ r)) x        ≡⟨ refl ⟩
         evalH ((-H P) ·X+ (- r)) x    ≡⟨ refl ⟩
         (evalH (-H P) x) · x + (- r)  ≡⟨ cong (λ u → (u · x) + (- r)) (-EvalDist P x) ⟩
         (- evalH P x) · x + (- r)     ≡⟨ cong (λ u → u + (- r)) (sym (-Comm· _ _)) ⟩
         - (evalH P x) · x + (- r)     ≡⟨ sym (-Dist+ _ _) ⟩
         - ((evalH P x) · x + r)       ≡⟨ refl ⟩
         - evalH (P ·X+ r) x ∎

  +HomEval : (P Q : RawHornerPolynomial νR) (x : ⟨ R ⟩)
    → evalH (P +H Q) x ≡ (evalH P x) + (evalH Q x)
  +HomEval 0H Q x = sym (+Lid _)
  +HomEval (P ·X+ r) 0H x = sym (+Rid _)
  +HomEval (P ·X+ r) (Q ·X+ s) x =
    evalH ((P +H Q) ·X+ (r + s)) x              ≡⟨ refl ⟩
    evalH (P +H Q) x · x + (r + s)              ≡⟨ cong (λ u → (u · x) + (r + s))
                                                        (+HomEval P Q x) ⟩
    (evalH P x + evalH Q x) · x + (r + s)       ≡⟨ cong (λ u → u + (r + s)) (·DistL+ _ _ _) ⟩
    (evalH P x) · x + (evalH Q x) · x + (r + s) ≡⟨ +ShufflePairs _ _ _ _ ⟩
    evalH (P ·X+ r) x + evalH (Q ·X+ s) x ∎

  ⋆0LeftAnnihilates : (P : RawHornerPolynomial νR) (x : ⟨ R ⟩)
    → evalH (0r ⋆ P) x ≡ 0r
  ⋆0LeftAnnihilates 0H x = refl
  ⋆0LeftAnnihilates (P ·X+ r) x =
    evalH ((0r ⋆ P) ·X+ (0r · r)) x ≡⟨ cong (λ u → evalH ((0r ⋆ P) ·X+ u) x)
                                            (0LeftAnnihilates _) ⟩
    evalH ((0r ⋆ P) ·X+ 0r) x       ≡⟨ refl ⟩
    (evalH (0r ⋆ P) x) · x + 0r     ≡⟨ +Rid _ ⟩
    (evalH (0r ⋆ P) x) · x          ≡⟨ cong (λ u → u · x)
                                            (⋆0LeftAnnihilates P x) ⟩
    0r · x                          ≡⟨ 0LeftAnnihilates _ ⟩
    0r ∎

  ⋆HomEval :  (r : ⟨ R ⟩) (P : RawHornerPolynomial νR) (x : ⟨ R ⟩)
           → evalH (r ⋆ P) x ≡ r · evalH P x
  ⋆HomEval r 0H x = 0r ≡⟨ sym (0RightAnnihilates _) ⟩ r · 0r ∎
  ⋆HomEval r (P ·X+ s) x =
    (evalH (r ⋆ P) x) · x + (r · s) ≡⟨ cong (λ u → (u · x) + (r · s)) (⋆HomEval r P x) ⟩
    r · (evalH P x) · x + (r · s)   ≡⟨ cong (λ u → u + (r · s)) (sym (·Assoc _ _ _)) ⟩
    r · ((evalH P x) · x) + (r · s) ≡⟨ sym (·DistR+ r _ _) ⟩
    r · ((evalH P x) · x + s)       ≡⟨ refl ⟩
    r · evalH (P ·X+ s) x ∎

  ·HomEval : (P Q : RawHornerPolynomial νR) (x : ⟨ R ⟩)
    → evalH (P ·H Q) x ≡ (evalH P x) · (evalH Q x)
  ·HomEval 0H Q x = 0r ≡⟨ sym (0LeftAnnihilates _) ⟩ 0r · evalH Q x ∎
  ·HomEval (P ·X+ r) Q x =
    evalH (((P ·H Q) ·X+ 0r) +H (r ⋆ Q)) x           ≡⟨ +HomEval ((P ·H Q) ·X+ 0r) (r ⋆ Q) x ⟩
    evalH ((P ·H Q) ·X+ 0r) x + evalH (r ⋆ Q) x      ≡⟨ cong (λ u → u + evalH (r ⋆ Q) x)
                                                             (+Rid _) ⟩
    (evalH (P ·H Q) x) · x + evalH (r ⋆ Q) x         ≡⟨ cong (λ u → (u · x) + evalH (r ⋆ Q) x)
                                                             (·HomEval P Q x) ⟩
    (evalH P x) · (evalH Q x) · x + evalH (r ⋆ Q) x  ≡⟨ cong (λ u → u + evalH (r ⋆ Q) x)
                                                             (sym (·CommRight _ _ _)) ⟩
    (evalH P x) · x · (evalH Q x) + evalH (r ⋆ Q) x  ≡⟨ cong
                                                         (λ u →
                                                           ((evalH P x · x) · evalH Q x) + u)
                                                         (⋆HomEval r Q x) ⟩
    (evalH P x) · x · (evalH Q x) + r · evalH Q x    ≡⟨ sym (·DistL+ _ _ _) ⟩
    ((evalH P x) · x + r) · evalH Q x                ≡⟨ refl ⟩
    evalH (P ·X+ r) x · evalH Q x ∎
