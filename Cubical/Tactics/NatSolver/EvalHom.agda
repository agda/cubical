{-# OPTIONS --safe #-}
module Cubical.Tactics.NatSolver.EvalHom where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Vec

open import Cubical.Tactics.NatSolver.HornerForms

private
  variable
    ℓ : Level

module HomomorphismProperties where
  open IteratedHornerOperations

  evalHom+0 : {n : ℕ} (P : IteratedHornerForms n) (xs : Vec ℕ n)
      → eval (0ₕ +ₕ P) xs ≡ eval P xs
  evalHom+0 (const x) [] = refl
  evalHom+0 _ (x ∷ xs) = refl

  eval0H : {n : ℕ} (xs : Vec ℕ n)
         → eval 0ₕ xs ≡ 0
  eval0H [] = refl
  eval0H (x ∷ xs) = refl

  eval1ₕ : {n : ℕ} (xs : Vec ℕ n)
         → eval 1ₕ xs ≡ 1
  eval1ₕ [] = refl
  eval1ₕ (x ∷ xs) =
    eval 1ₕ (x ∷ xs)                             ≡⟨ refl ⟩
    eval (0H ·X+ 1ₕ) (x ∷ xs)                    ≡⟨ refl ⟩
    eval 0H (x ∷ xs) · x + eval 1ₕ xs            ≡⟨ cong (λ u → u · x + eval 1ₕ xs)
                                                        (eval0H (x ∷ xs)) ⟩
    0 · x + eval 1ₕ xs                           ≡⟨ cong (λ u → 0 · x + u)
                                                        (eval1ₕ xs) ⟩
    1 ∎


  +ShufflePairs : (a b c d : ℕ)
                → (a + b) + (c + d) ≡ (a + c) + (b + d)
  +ShufflePairs a b c d =
    (a + b) + (c + d) ≡⟨ +-assoc (a + b) c d ⟩
    ((a + b) + c) + d ≡⟨ cong (λ u → u + d) (sym (+-assoc a b c)) ⟩
    (a + (b + c)) + d ≡⟨ cong (λ u → (a + u) + d) (+-comm b c) ⟩
    (a + (c + b)) + d ≡⟨ cong (λ u → u + d) (+-assoc a c b) ⟩
    ((a + c) + b) + d ≡⟨ sym (+-assoc (a + c) b d) ⟩
    (a + c) + (b + d) ∎

  +Homeval :
    {n : ℕ} (P Q : IteratedHornerForms n) (xs : Vec ℕ n)
    → eval (P +ₕ Q) xs ≡ (eval P xs) + (eval Q xs)
  +Homeval (const x) (const y) [] = refl
  +Homeval 0H Q xs =
    eval (0H +ₕ Q) xs            ≡⟨ refl ⟩
    0 + eval Q xs               ≡⟨ cong (λ u → u + eval Q xs) (sym (eval0H xs)) ⟩
    eval 0H xs + eval Q xs ∎
  +Homeval (P ·X+ Q) 0H xs =
    eval ((P ·X+ Q) +ₕ 0H) xs       ≡⟨ refl ⟩
    eval (P ·X+ Q) xs              ≡⟨ sym (+-zero _) ⟩
    eval (P ·X+ Q) xs + 0          ≡⟨ cong (λ u → eval (P ·X+ Q) xs + u)
                                           (sym (eval0H xs)) ⟩
    eval (P ·X+ Q) xs + eval 0H xs ∎
  +Homeval (P ·X+ Q) (S ·X+ T) (x ∷ xs) =
    eval ((P ·X+ Q) +ₕ (S ·X+ T)) (x ∷ xs)
   ≡⟨ refl ⟩
    eval ((P +ₕ S) ·X+ (Q +ₕ T)) (x ∷ xs)
   ≡⟨ refl ⟩
    (eval (P +ₕ S) (x ∷ xs)) · x + eval (Q +ₕ T) xs
   ≡⟨ cong (λ u → (eval (P +ₕ S) (x ∷ xs)) · x + u) (+Homeval Q T xs) ⟩
    (eval (P +ₕ S) (x ∷ xs)) · x + (eval Q xs + eval T xs)
   ≡⟨ cong (λ u → u · x + (eval Q xs + eval T xs)) (+Homeval P S (x ∷ xs)) ⟩
    (eval P (x ∷ xs) + eval S (x ∷ xs)) · x
    + (eval Q xs + eval T xs)
   ≡⟨ cong (λ u → u + (eval Q xs + eval T xs))
     (sym (·-distribʳ (eval P (x ∷ xs)) (eval S (x ∷ xs)) x)) ⟩
    (eval P (x ∷ xs)) · x + (eval S (x ∷ xs)) · x
    + (eval Q xs + eval T xs)
   ≡⟨ +ShufflePairs ((eval P (x ∷ xs)) · x) ((eval S (x ∷ xs)) · x) (eval Q xs) (eval T xs) ⟩
    ((eval P (x ∷ xs)) · x + eval Q xs)
    + ((eval S (x ∷ xs)) · x + eval T xs)
   ∎

  ⋆Homeval : {n : ℕ}
             (r : IteratedHornerForms n)
             (P : IteratedHornerForms (ℕ.suc n)) (x : ℕ) (xs : Vec ℕ n)
           → eval (r ⋆ P) (x ∷ xs) ≡ eval r xs · eval P (x ∷ xs)


  ⋆0LeftAnnihilates :
    {n : ℕ} (P : IteratedHornerForms (ℕ.suc n)) (xs : Vec ℕ (ℕ.suc n))
    → eval (0ₕ ⋆ P) xs ≡ 0

  ·Homeval : {n : ℕ} (P Q : IteratedHornerForms n) (xs : Vec ℕ n)
    → eval (P ·ₕ Q) xs ≡ (eval P xs) · (eval Q xs)

  ⋆0LeftAnnihilates 0H xs = eval0H xs
  ⋆0LeftAnnihilates (P ·X+ Q) (x ∷ xs) =
      eval (0ₕ ⋆ (P ·X+ Q)) (x ∷ xs)                    ≡⟨ refl ⟩
      eval ((0ₕ ⋆ P) ·X+ (0ₕ ·ₕ Q)) (x ∷ xs)             ≡⟨ refl ⟩
      (eval (0ₕ ⋆ P) (x ∷ xs)) · x + eval (0ₕ ·ₕ Q) xs
    ≡⟨ cong (λ u → (u · x) + eval (0ₕ ·ₕ Q) _) (⋆0LeftAnnihilates P (x ∷ xs)) ⟩
      0 · x + eval (0ₕ ·ₕ Q) xs
    ≡⟨ ·Homeval 0ₕ Q _ ⟩
      eval 0ₕ xs · eval Q xs
    ≡⟨ cong (λ u → u · eval Q xs) (eval0H xs) ⟩
      0 · eval Q xs ∎

  ⋆Homeval r 0H x xs =
    eval (r ⋆ 0H) (x ∷ xs)         ≡⟨ refl ⟩
    0                              ≡⟨ 0≡m·0 (eval r xs) ⟩
    eval r xs · 0                  ≡⟨ refl ⟩
    eval r xs · eval 0H (x ∷ xs) ∎
  ⋆Homeval r (P ·X+ Q) x xs =
      eval (r ⋆ (P ·X+ Q)) (x ∷ xs)                    ≡⟨ refl ⟩
      eval ((r ⋆ P) ·X+ (r ·ₕ Q)) (x ∷ xs)              ≡⟨ refl ⟩
      (eval (r ⋆ P) (x ∷ xs)) · x + eval (r ·ₕ Q) xs
    ≡⟨ cong (λ u → u · x + eval (r ·ₕ Q) xs) (⋆Homeval r P x xs) ⟩
      (eval r xs · eval P (x ∷ xs)) · x + eval (r ·ₕ Q) xs
    ≡⟨ cong (λ u → (eval r xs · eval P (x ∷ xs)) · x + u) (·Homeval r Q xs) ⟩
      (eval r xs · eval P (x ∷ xs)) · x + eval r xs · eval Q xs
    ≡⟨ cong (λ u → u  + eval r xs · eval Q xs) (sym (·-assoc (eval r xs) (eval P (x ∷ xs)) x)) ⟩
      eval r xs · (eval P (x ∷ xs) · x) + eval r xs · eval Q xs
    ≡⟨ ·-distribˡ (eval r xs)  ((eval P (x ∷ xs) · x)) (eval Q xs) ⟩
      eval r xs · ((eval P (x ∷ xs) · x) + eval Q xs)
    ≡⟨ refl ⟩
      eval r xs · eval (P ·X+ Q) (x ∷ xs) ∎

  combineCases :
    {n : ℕ} (Q : IteratedHornerForms n) (P S : IteratedHornerForms (ℕ.suc n))
    (xs : Vec ℕ (ℕ.suc n))
    → eval ((P ·X+ Q) ·ₕ S) xs ≡ eval (((P ·ₕ S) ·X+ 0ₕ) +ₕ (Q ⋆ S)) xs
  combineCases Q P S (x ∷ xs) with (P ·ₕ S)
  ... | 0H =
    eval (Q ⋆ S) (x ∷ xs)                ≡⟨ refl ⟩
    0 + eval (Q ⋆ S) (x ∷ xs)           ≡⟨ cong (λ u → u + eval (Q ⋆ S) (x ∷ xs)) lemma ⟩
    eval (0H ·X+ 0ₕ) (x ∷ xs)
    + eval (Q ⋆ S) (x ∷ xs)              ≡⟨ sym (+Homeval
                                                  (0H ·X+ 0ₕ) (Q ⋆ S) (x ∷ xs)) ⟩
    eval ((0H ·X+ 0ₕ) +ₕ (Q ⋆ S)) (x ∷ xs) ∎
    where lemma : 0 ≡ eval (0H ·X+ 0ₕ) (x ∷ xs)
          lemma = 0
                ≡⟨ refl ⟩
                  0 + 0
                ≡⟨ cong (λ u → u + 0) refl ⟩
                  0 · x + 0
                ≡⟨ cong (λ u → 0 · x + u) (sym (eval0H xs)) ⟩
                  0 · x + eval 0ₕ xs
                ≡⟨ cong (λ u → u · x + eval 0ₕ xs) (sym (eval0H (x ∷ xs))) ⟩
                  eval 0H (x ∷ xs) · x + eval 0ₕ xs
                ≡⟨ refl ⟩
                  eval (0H ·X+ 0ₕ) (x ∷ xs) ∎
  ... | (_ ·X+ _) = refl

  ·Homeval (const x) (const y) [] = refl
  ·Homeval 0H Q xs =
    eval (0H ·ₕ Q) xs        ≡⟨ eval0H xs ⟩
    0                                 ≡⟨ refl ⟩
    0 · eval Q xs          ≡⟨ cong (λ u → u · eval Q xs) (sym (eval0H xs)) ⟩
    eval 0H xs · eval Q xs ∎
  ·Homeval (P ·X+ Q) S (x ∷ xs) =
      eval ((P ·X+ Q) ·ₕ S) (x ∷ xs)
    ≡⟨ combineCases Q P S (x ∷ xs) ⟩
      eval (((P ·ₕ S) ·X+ 0ₕ) +ₕ (Q ⋆ S)) (x ∷ xs)
    ≡⟨ +Homeval ((P ·ₕ S) ·X+ 0ₕ) (Q ⋆ S) (x ∷ xs) ⟩
      eval ((P ·ₕ S) ·X+ 0ₕ) (x ∷ xs) + eval (Q ⋆ S) (x ∷ xs)
    ≡⟨ refl ⟩
      (eval (P ·ₕ S) (x ∷ xs) · x + eval 0ₕ xs)
      + eval (Q ⋆ S) (x ∷ xs)
    ≡⟨ cong (λ u → u + eval (Q ⋆ S) (x ∷ xs))
          ((eval (P ·ₕ S) (x ∷ xs) · x + eval 0ₕ xs)
         ≡⟨ cong (λ u → eval (P ·ₕ S) (x ∷ xs) · x + u) (eval0H xs) ⟩
           (eval (P ·ₕ S) (x ∷ xs) · x + 0)
         ≡⟨ +-zero _ ⟩
           (eval (P ·ₕ S) (x ∷ xs) · x)
         ≡⟨ cong (λ u → u · x) (·Homeval P S (x ∷ xs)) ⟩
           ((eval P (x ∷ xs) · eval S (x ∷ xs)) · x)
         ≡⟨ sym (·-assoc (eval P (x ∷ xs)) (eval S (x ∷ xs)) x) ⟩
           (eval P (x ∷ xs) · (eval S (x ∷ xs) · x))
         ≡⟨ cong (λ u → eval P (x ∷ xs) · u) (·-comm _ x) ⟩
           (eval P (x ∷ xs) · (x · eval S (x ∷ xs)))
         ≡⟨ ·-assoc (eval P (x ∷ xs)) x (eval S (x ∷ xs)) ⟩
           (eval P (x ∷ xs) · x) · eval S (x ∷ xs)
          ∎) ⟩
      (eval P (x ∷ xs) · x) · eval S (x ∷ xs)
      + eval (Q ⋆ S) (x ∷ xs)
    ≡⟨ cong (λ u → (eval P (x ∷ xs) · x) · eval S (x ∷ xs) + u)
            (⋆Homeval Q S x xs) ⟩
      (eval P (x ∷ xs) · x) · eval S (x ∷ xs)
      + eval Q xs · eval S (x ∷ xs)
    ≡⟨ ·-distribʳ (eval P (x ∷ xs) · x) (eval Q xs) (eval S (x ∷ xs)) ⟩
      ((eval P (x ∷ xs) · x) + eval Q xs) · eval S (x ∷ xs)
    ≡⟨ refl ⟩
      eval (P ·X+ Q) (x ∷ xs) · eval S (x ∷ xs) ∎
