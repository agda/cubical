{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.MultivariateEvaluationHomomorphism where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData
open import Cubical.Data.Vec

open import Cubical.Algebra.RingSolver.RawRing
open import Cubical.Algebra.RingSolver.AlmostRing renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Algebra.RingSolver.HornerNormalForm
open import Cubical.Algebra.RingSolver.IteratedHornerForms

private
  variable
    ℓ : Level

module HomomorphismProperties (R : AlmostRing {ℓ}) where
  private
    νR = AlmostRing→RawRing R
  open AlmostRing R
  open Theory R
  open IteratedHornerOperations νR

  EvalHom+0 : (n : ℕ) (P : IteratedHornerForms νR n) (xs : Vec ⟨ νR ⟩ n)
      → Eval n (0H +H P) xs ≡ Eval n P xs
  EvalHom+0 n P xs = refl

  Eval0H : (n : ℕ) (xs : Vec ⟨ νR ⟩ n)
         → Eval {R = νR} n 0H xs ≡ 0r
  Eval0H .ℕ.zero [] = refl
  Eval0H .(ℕ.suc _) (x ∷ xs) = refl

  -EvalDist :
    (n : ℕ) (P : IteratedHornerForms νR n) (xs : Vec ⟨ νR ⟩ n)
    → Eval n (-H P) xs ≡ - Eval n P xs
  -EvalDist .ℕ.zero (const x) []   = refl
  -EvalDist          n       0H  xs =
    Eval n (-H 0H) xs  ≡⟨ Eval0H n xs ⟩
    0r                        ≡⟨ sym 0IsSelfinverse ⟩
    - 0r                      ≡⟨ cong -_ (sym (Eval0H n xs)) ⟩
    - Eval n 0H xs     ∎
  -EvalDist .(ℕ.suc _) (P ·X+ Q) (x ∷ xs) =
      Eval (ℕ.suc _) (-H (P ·X+ Q)) (x ∷ xs)
    ≡⟨ refl ⟩
      Eval (ℕ.suc _) ((-H P) ·X+ (-H Q)) (x ∷ xs)
    ≡⟨ refl ⟩
      (Eval (ℕ.suc _) (-H P) (x ∷ xs)) · x + Eval _ (-H Q) xs
    ≡⟨ cong (λ u → u · x + Eval _ (-H Q) xs) (-EvalDist _ P _) ⟩
      (- Eval (ℕ.suc _) P (x ∷ xs)) · x + Eval _ (-H Q) xs
    ≡⟨ cong (λ u → (- Eval (ℕ.suc _) P (x ∷ xs)) · x + u) (-EvalDist _ Q _) ⟩
      (- Eval (ℕ.suc _) P (x ∷ xs)) · x + - Eval _ Q xs
    ≡⟨ cong (λ u → u + - Eval _ Q xs) (sym (-Comm· _ _)) ⟩
      - (Eval (ℕ.suc _) P (x ∷ xs)) · x + - Eval _ Q xs
    ≡⟨ sym (-Dist+ _ _) ⟩
      - ((Eval (ℕ.suc _) P (x ∷ xs)) · x + Eval _ Q xs)
    ≡⟨ refl ⟩
      - Eval (ℕ.suc _) (P ·X+ Q) (x ∷ xs) ∎

  +HomEval :
    (n : ℕ) (P Q : IteratedHornerForms νR n) (xs : Vec ⟨ νR ⟩ n)
    → Eval n (P +H Q) xs ≡ (Eval n P xs) + (Eval n Q xs)
  +HomEval .ℕ.zero (const x) (const y) [] = refl
  +HomEval .ℕ.zero (const x) 0H [] = sym (+Rid _)
  +HomEval n 0H Q xs =
    Eval n (0H +H Q) xs            ≡⟨ refl ⟩
    Eval n Q xs                    ≡⟨ sym (+Lid _) ⟩
    0r + Eval n Q xs               ≡⟨ cong (λ u → u + Eval n Q xs) (sym (Eval0H n xs)) ⟩
    Eval n 0H xs + Eval n Q xs ∎
  +HomEval .(ℕ.suc _) (P ·X+ Q) 0H xs =
    Eval (ℕ.suc _) ((P ·X+ Q) +H 0H) xs                    ≡⟨ refl ⟩
    Eval (ℕ.suc _) (P ·X+ Q) xs                            ≡⟨ sym (+Rid _) ⟩
    Eval (ℕ.suc _) (P ·X+ Q) xs + 0r
   ≡⟨ cong (λ u → Eval (ℕ.suc _) (P ·X+ Q) xs + u) (sym (Eval0H _ xs)) ⟩
    Eval (ℕ.suc _) (P ·X+ Q) xs + Eval (ℕ.suc _) 0H xs ∎
  +HomEval .(ℕ.suc _) (P ·X+ Q) (S ·X+ T) (x ∷ xs) =
    Eval (ℕ.suc _) ((P ·X+ Q) +H (S ·X+ T)) (x ∷ xs)
   ≡⟨ refl ⟩
    Eval (ℕ.suc _) ((P +H S) ·X+ (Q +H T)) (x ∷ xs)
   ≡⟨ refl ⟩
    (Eval (ℕ.suc _) (P +H S) (x ∷ xs)) · x + Eval _ (Q +H T) xs
   ≡⟨ cong (λ u → (Eval (ℕ.suc _) (P +H S) (x ∷ xs)) · x + u) (+HomEval _ Q T xs) ⟩
    (Eval (ℕ.suc _) (P +H S) (x ∷ xs)) · x + (Eval _ Q xs + Eval _ T xs)
   ≡⟨ cong (λ u → u · x + (Eval _ Q xs + Eval _ T xs)) (+HomEval (ℕ.suc _) P S (x ∷ xs)) ⟩
    (Eval (ℕ.suc _) P (x ∷ xs) + Eval (ℕ.suc _) S (x ∷ xs)) · x
    + (Eval _ Q xs + Eval _ T xs)
   ≡⟨ cong (λ u → u + (Eval _ Q xs + Eval _ T xs)) (·DistL+ _ _ _) ⟩
    (Eval (ℕ.suc _) P (x ∷ xs)) · x + (Eval (ℕ.suc _) S (x ∷ xs)) · x
    + (Eval _ Q xs + Eval _ T xs)
   ≡⟨ +ShufflePairs _ _ _ _ ⟩
    ((Eval (ℕ.suc _) P (x ∷ xs)) · x + Eval _ Q xs)
    + ((Eval (ℕ.suc _) S (x ∷ xs)) · x + Eval _ T xs)
   ≡⟨ refl ⟩
    Eval (ℕ.suc _) (P ·X+ Q) (x ∷ xs)
    + Eval (ℕ.suc _) (S ·X+ T) (x ∷ xs) ∎


