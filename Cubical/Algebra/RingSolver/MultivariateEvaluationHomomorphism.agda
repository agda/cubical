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
      → Eval n (0ₕ +ₕ P) xs ≡ Eval n P xs
  EvalHom+0 ℕ.zero (const x) [] = +Lid _
  EvalHom+0 (ℕ.suc n) P xs = refl

  Eval0H : (n : ℕ) (xs : Vec ⟨ νR ⟩ n)
         → Eval {R = νR} n 0ₕ xs ≡ 0r
  Eval0H .ℕ.zero [] = refl
  Eval0H .(ℕ.suc _) (x ∷ xs) = refl

  -EvalDist :
    (n : ℕ) (P : IteratedHornerForms νR n) (xs : Vec ⟨ νR ⟩ n)
    → Eval n (-ₕ P) xs ≡ - Eval n P xs
  -EvalDist .ℕ.zero (const x) []   = refl
  -EvalDist          n       0H  xs =
    Eval n (-ₕ 0H) xs  ≡⟨ Eval0H n xs ⟩
    0r                        ≡⟨ sym 0IsSelfinverse ⟩
    - 0r                      ≡⟨ cong -_ (sym (Eval0H n xs)) ⟩
    - Eval n 0H xs     ∎
  -EvalDist .(ℕ.suc _) (P ·X+ Q) (x ∷ xs) =
      Eval (ℕ.suc _) (-ₕ (P ·X+ Q)) (x ∷ xs)
    ≡⟨ refl ⟩
      Eval (ℕ.suc _) ((-ₕ P) ·X+ (-ₕ Q)) (x ∷ xs)
    ≡⟨ refl ⟩
      (Eval (ℕ.suc _) (-ₕ P) (x ∷ xs)) · x + Eval _ (-ₕ Q) xs
    ≡⟨ cong (λ u → u · x + Eval _ (-ₕ Q) xs) (-EvalDist _ P _) ⟩
      (- Eval (ℕ.suc _) P (x ∷ xs)) · x + Eval _ (-ₕ Q) xs
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
    → Eval n (P +ₕ Q) xs ≡ (Eval n P xs) + (Eval n Q xs)
  +HomEval .ℕ.zero (const x) (const y) [] = refl
  +HomEval n 0H Q xs =
    Eval n (0H +ₕ Q) xs            ≡⟨ refl ⟩
    Eval n Q xs                    ≡⟨ sym (+Lid _) ⟩
    0r + Eval n Q xs               ≡⟨ cong (λ u → u + Eval n Q xs) (sym (Eval0H n xs)) ⟩
    Eval n 0H xs + Eval n Q xs ∎
  +HomEval .(ℕ.suc _) (P ·X+ Q) 0H xs =
    Eval (ℕ.suc _) ((P ·X+ Q) +ₕ 0H) xs                    ≡⟨ refl ⟩
    Eval (ℕ.suc _) (P ·X+ Q) xs                            ≡⟨ sym (+Rid _) ⟩
    Eval (ℕ.suc _) (P ·X+ Q) xs + 0r
   ≡⟨ cong (λ u → Eval (ℕ.suc _) (P ·X+ Q) xs + u) (sym (Eval0H _ xs)) ⟩
    Eval (ℕ.suc _) (P ·X+ Q) xs + Eval (ℕ.suc _) 0H xs ∎
  +HomEval .(ℕ.suc _) (P ·X+ Q) (S ·X+ T) (x ∷ xs) =
    Eval (ℕ.suc _) ((P ·X+ Q) +ₕ (S ·X+ T)) (x ∷ xs)
   ≡⟨ refl ⟩
    Eval (ℕ.suc _) ((P +ₕ S) ·X+ (Q +ₕ T)) (x ∷ xs)
   ≡⟨ refl ⟩
    (Eval (ℕ.suc _) (P +ₕ S) (x ∷ xs)) · x + Eval _ (Q +ₕ T) xs
   ≡⟨ cong (λ u → (Eval (ℕ.suc _) (P +ₕ S) (x ∷ xs)) · x + u) (+HomEval _ Q T xs) ⟩
    (Eval (ℕ.suc _) (P +ₕ S) (x ∷ xs)) · x + (Eval _ Q xs + Eval _ T xs)
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

  ⋆HomEval : (n : ℕ)
             (r : IteratedHornerForms νR n)
             (P : IteratedHornerForms νR (ℕ.suc n)) (x : ⟨ νR ⟩) (xs : Vec ⟨ νR ⟩ n)
           → Eval (ℕ.suc n) (r ⋆ P) (x ∷ xs) ≡ Eval n r xs · Eval (ℕ.suc n) P (x ∷ xs)

  ⋆0LeftAnnihilates :
    (n : ℕ) (P : IteratedHornerForms νR (ℕ.suc n)) (xs : Vec ⟨ νR ⟩ (ℕ.suc n))
    → Eval (ℕ.suc n) (0ₕ ⋆ P) xs ≡ 0r
  ·HomEval : (n : ℕ) (P Q : IteratedHornerForms νR n) (xs : Vec ⟨ νR ⟩ n)
    → Eval n (P ·ₕ Q) xs ≡ (Eval n P xs) · (Eval n Q xs)

  ⋆0LeftAnnihilates n 0H xs = Eval0H (ℕ.suc n) xs
  ⋆0LeftAnnihilates n (P ·X+ Q) (x ∷ xs) =
      Eval (ℕ.suc n) (0ₕ ⋆ (P ·X+ Q)) (x ∷ xs)                    ≡⟨ refl ⟩
      Eval (ℕ.suc n) ((0ₕ ⋆ P) ·X+ (0ₕ ·ₕ Q)) (x ∷ xs)             ≡⟨ refl ⟩
      (Eval (ℕ.suc n) (0ₕ ⋆ P) (x ∷ xs)) · x + Eval n (0ₕ ·ₕ Q) xs
    ≡⟨ cong (λ u → (u · x) + Eval _ (0ₕ ·ₕ Q) _) (⋆0LeftAnnihilates n P (x ∷ xs)) ⟩
      0r · x + Eval n (0ₕ ·ₕ Q) xs
    ≡⟨ cong (λ u → u + Eval _ (0ₕ ·ₕ Q) _) (0LeftAnnihilates _) ⟩
      0r + Eval n (0ₕ ·ₕ Q) xs
    ≡⟨ +Lid _ ⟩
      Eval n (0ₕ ·ₕ Q) xs
    ≡⟨ ·HomEval n 0ₕ Q _ ⟩
      Eval n 0ₕ xs · Eval n Q xs
    ≡⟨ cong (λ u → u · Eval n Q xs) (Eval0H _ xs) ⟩
      0r · Eval n Q xs
    ≡⟨ 0LeftAnnihilates _ ⟩
      0r ∎

  ⋆HomEval n r 0H x xs =
    Eval (ℕ.suc n) (r ⋆ 0H) (x ∷ xs)         ≡⟨ refl ⟩
    0r                                       ≡⟨ sym (0RightAnnihilates _) ⟩
    Eval n r xs · 0r                         ≡⟨ refl ⟩
    Eval n r xs · Eval {R = νR} (ℕ.suc n) 0H (x ∷ xs) ∎
  ⋆HomEval n r (P ·X+ Q) x xs =
      Eval (ℕ.suc n) (r ⋆ (P ·X+ Q)) (x ∷ xs)                    ≡⟨ refl ⟩
      Eval (ℕ.suc n) ((r ⋆ P) ·X+ (r ·ₕ Q)) (x ∷ xs)              ≡⟨ refl ⟩
      (Eval (ℕ.suc n) (r ⋆ P) (x ∷ xs)) · x + Eval n (r ·ₕ Q) xs
    ≡⟨ cong (λ u → u · x + Eval n (r ·ₕ Q) xs) (⋆HomEval n r P x xs) ⟩
      (Eval n r xs · Eval (ℕ.suc n) P (x ∷ xs)) · x + Eval n (r ·ₕ Q) xs
    ≡⟨ cong (λ u → (Eval n r xs · Eval (ℕ.suc n) P (x ∷ xs)) · x + u) (·HomEval n r Q xs) ⟩
      (Eval n r xs · Eval (ℕ.suc n) P (x ∷ xs)) · x + Eval n r xs · Eval n Q xs
    ≡⟨ cong (λ u → u  + Eval n r xs · Eval n Q xs) (sym (·Assoc _ _ _)) ⟩
      Eval n r xs · (Eval (ℕ.suc n) P (x ∷ xs) · x) + Eval n r xs · Eval n Q xs
    ≡⟨ sym (·DistR+ _ _ _) ⟩
      Eval n r xs · ((Eval (ℕ.suc n) P (x ∷ xs) · x) + Eval n Q xs)
    ≡⟨ refl ⟩
      Eval n r xs · Eval (ℕ.suc n) (P ·X+ Q) (x ∷ xs) ∎

  ·HomEval .ℕ.zero (const x) (const y) [] = refl
  ·HomEval (ℕ.suc n) 0H Q xs =
    Eval (ℕ.suc n) (0H ·ₕ Q) xs        ≡⟨ Eval0H _ xs ⟩
    0r                                 ≡⟨ sym (0LeftAnnihilates _) ⟩
    0r · Eval (ℕ.suc n) Q xs          ≡⟨ cong (λ u → u · Eval _ Q xs) (sym (Eval0H _ xs)) ⟩
    Eval (ℕ.suc n) 0H xs · Eval (ℕ.suc n) Q xs ∎
  ·HomEval (ℕ.suc n) (P ·X+ Q) S (x ∷ xs) =
      Eval (ℕ.suc n) ((P ·X+ Q) ·ₕ S) (x ∷ xs)
    ≡⟨ refl ⟩
      Eval (ℕ.suc n) (((P ·ₕ S) ·X+ 0ₕ) +ₕ (Q ⋆ S)) (x ∷ xs)
    ≡⟨ +HomEval (ℕ.suc n) ((P ·ₕ S) ·X+ 0ₕ) (Q ⋆ S) (x ∷ xs) ⟩
      Eval (ℕ.suc n) ((P ·ₕ S) ·X+ 0ₕ) (x ∷ xs) + Eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)
    ≡⟨ refl ⟩
      (Eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x + Eval n 0ₕ xs)
      + Eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)
    ≡⟨ cong (λ u → u + Eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs))
          ((Eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x + Eval n 0ₕ xs)
         ≡⟨ cong (λ u → Eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x + u) (Eval0H _ xs) ⟩
           (Eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x + 0r)
         ≡⟨ +Rid _ ⟩
           (Eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x)
         ≡⟨ cong (λ u → u · x) (·HomEval (ℕ.suc n) P S (x ∷ xs)) ⟩
           ((Eval (ℕ.suc n) P (x ∷ xs) · Eval (ℕ.suc n) S (x ∷ xs)) · x)
         ≡⟨ sym (·Assoc _ _ _) ⟩
           (Eval (ℕ.suc n) P (x ∷ xs) · (Eval (ℕ.suc n) S (x ∷ xs) · x))
         ≡⟨ cong (λ u → Eval (ℕ.suc n) P (x ∷ xs) · u) (·Comm _ _) ⟩
           (Eval (ℕ.suc n) P (x ∷ xs) · (x · Eval (ℕ.suc n) S (x ∷ xs)))
         ≡⟨ ·Assoc _ _ _ ⟩
           (Eval (ℕ.suc n) P (x ∷ xs) · x) · Eval (ℕ.suc n) S (x ∷ xs)
          ∎) ⟩
      (Eval (ℕ.suc n) P (x ∷ xs) · x) · Eval (ℕ.suc n) S (x ∷ xs)
      + Eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)
    ≡⟨ cong (λ u → (Eval (ℕ.suc n) P (x ∷ xs) · x) · Eval (ℕ.suc n) S (x ∷ xs) + u)
            (⋆HomEval n Q S x xs) ⟩
      (Eval (ℕ.suc n) P (x ∷ xs) · x) · Eval (ℕ.suc n) S (x ∷ xs)
      + Eval n Q xs · Eval (ℕ.suc n) S (x ∷ xs)
    ≡⟨ sym (·DistL+ _ _ _) ⟩
      ((Eval (ℕ.suc n) P (x ∷ xs) · x) + Eval n Q xs) · Eval (ℕ.suc n) S (x ∷ xs)
    ≡⟨ refl ⟩
      Eval (ℕ.suc n) (P ·X+ Q) (x ∷ xs) · Eval (ℕ.suc n) S (x ∷ xs) ∎
