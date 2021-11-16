{-# OPTIONS --safe #-}
module Cubical.Algebra.NatSolver.EvaluationHomomorphism where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Vec

open import Cubical.Algebra.NatSolver.HornerForms

private
  variable
    ℓ : Level

module HomomorphismProperties where
  open IteratedHornerOperations

  evalHom+0 : (n : ℕ) (P : IteratedHornerForms n) (xs : Vec ℕ n)
      → eval n (0ₕ +ₕ P) xs ≡ eval n P xs
  evalHom+0 ℕ.zero (const x) [] = refl
  evalHom+0 (ℕ.suc n) P xs = refl

  eval0H : (n : ℕ) (xs : Vec ℕ n)
         → eval n 0ₕ xs ≡ 0
  eval0H .ℕ.zero [] = refl
  eval0H .(ℕ.suc _) (x ∷ xs) = refl

  eval1ₕ : (n : ℕ) (xs : Vec ℕ n)
         → eval n 1ₕ xs ≡ 1
  eval1ₕ .ℕ.zero [] = refl
  eval1ₕ (ℕ.suc n) (x ∷ xs) =
    eval (ℕ.suc n) 1ₕ (x ∷ xs)                             ≡⟨ refl ⟩
    eval (ℕ.suc n) (0H ·X+ 1ₕ) (x ∷ xs)                    ≡⟨ refl ⟩
    eval (ℕ.suc n) 0H (x ∷ xs) · x + eval n 1ₕ xs ≡⟨ cong (λ u → u · x + eval n 1ₕ xs)
                                                                   (eval0H _ (x ∷ xs)) ⟩
    0 · x + eval n 1ₕ xs                                   ≡⟨ cong (λ u → 0 · x + u)
                                                                    (eval1ₕ _ xs) ⟩
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
    (n : ℕ) (P Q : IteratedHornerForms n) (xs : Vec ℕ n)
    → eval n (P +ₕ Q) xs ≡ (eval n P xs) + (eval n Q xs)
  +Homeval .ℕ.zero (const x) (const y) [] = refl
  +Homeval n 0H Q xs =
    eval n (0H +ₕ Q) xs            ≡⟨ refl ⟩
    0 + eval n Q xs               ≡⟨ cong (λ u → u + eval n Q xs) (sym (eval0H n xs)) ⟩
    eval n 0H xs + eval n Q xs ∎
  +Homeval .(ℕ.suc _) (P ·X+ Q) 0H xs =
    eval (ℕ.suc _) ((P ·X+ Q) +ₕ 0H) xs                    ≡⟨ refl ⟩
    eval (ℕ.suc _) (P ·X+ Q) xs                            ≡⟨ sym (+-zero _) ⟩
    eval (ℕ.suc _) (P ·X+ Q) xs + 0
   ≡⟨ cong (λ u → eval (ℕ.suc _) (P ·X+ Q) xs + u) (sym (eval0H _ xs)) ⟩
    eval (ℕ.suc _) (P ·X+ Q) xs + eval (ℕ.suc _) 0H xs ∎
  +Homeval .(ℕ.suc _) (P ·X+ Q) (S ·X+ T) (x ∷ xs) =
    eval (ℕ.suc _) ((P ·X+ Q) +ₕ (S ·X+ T)) (x ∷ xs)
   ≡⟨ refl ⟩
    eval (ℕ.suc _) ((P +ₕ S) ·X+ (Q +ₕ T)) (x ∷ xs)
   ≡⟨ refl ⟩
    (eval (ℕ.suc _) (P +ₕ S) (x ∷ xs)) · x + eval _ (Q +ₕ T) xs
   ≡⟨ cong (λ u → (eval (ℕ.suc _) (P +ₕ S) (x ∷ xs)) · x + u) (+Homeval _ Q T xs) ⟩
    (eval (ℕ.suc _) (P +ₕ S) (x ∷ xs)) · x + (eval _ Q xs + eval _ T xs)
   ≡⟨ cong (λ u → u · x + (eval _ Q xs + eval _ T xs)) (+Homeval (ℕ.suc _) P S (x ∷ xs)) ⟩
    (eval (ℕ.suc _) P (x ∷ xs) + eval (ℕ.suc _) S (x ∷ xs)) · x
    + (eval _ Q xs + eval _ T xs)
   ≡⟨ cong (λ u → u + (eval _ Q xs + eval _ T xs))
     (sym (·-distribʳ (eval (ℕ.suc _) P (x ∷ xs)) (eval (ℕ.suc _) S (x ∷ xs)) x)) ⟩
    (eval (ℕ.suc _) P (x ∷ xs)) · x + (eval (ℕ.suc _) S (x ∷ xs)) · x
    + (eval _ Q xs + eval _ T xs)
   ≡⟨ +ShufflePairs ((eval (ℕ.suc _) P (x ∷ xs)) · x) ((eval (ℕ.suc _) S (x ∷ xs)) · x) (eval _ Q xs) (eval _ T xs) ⟩
    ((eval (ℕ.suc _) P (x ∷ xs)) · x + eval _ Q xs)
    + ((eval (ℕ.suc _) S (x ∷ xs)) · x + eval _ T xs)
   ∎

  ⋆Homeval : (n : ℕ)
             (r : IteratedHornerForms n)
             (P : IteratedHornerForms (ℕ.suc n)) (x : ℕ) (xs : Vec ℕ n)
           → eval (ℕ.suc n) (r ⋆ P) (x ∷ xs) ≡ eval n r xs · eval (ℕ.suc n) P (x ∷ xs)


  ⋆0LeftAnnihilates :
    (n : ℕ) (P : IteratedHornerForms (ℕ.suc n)) (xs : Vec ℕ (ℕ.suc n))
    → eval (ℕ.suc n) (0ₕ ⋆ P) xs ≡ 0

  ·Homeval : (n : ℕ) (P Q : IteratedHornerForms n) (xs : Vec ℕ n)
    → eval n (P ·ₕ Q) xs ≡ (eval n P xs) · (eval n Q xs)

  ⋆0LeftAnnihilates n 0H xs = eval0H (ℕ.suc n) xs
  ⋆0LeftAnnihilates n (P ·X+ Q) (x ∷ xs) =
      eval (ℕ.suc n) (0ₕ ⋆ (P ·X+ Q)) (x ∷ xs)                    ≡⟨ refl ⟩
      eval (ℕ.suc n) ((0ₕ ⋆ P) ·X+ (0ₕ ·ₕ Q)) (x ∷ xs)             ≡⟨ refl ⟩
      (eval (ℕ.suc n) (0ₕ ⋆ P) (x ∷ xs)) · x + eval n (0ₕ ·ₕ Q) xs
    ≡⟨ cong (λ u → (u · x) + eval _ (0ₕ ·ₕ Q) _) (⋆0LeftAnnihilates n P (x ∷ xs)) ⟩
      0 · x + eval n (0ₕ ·ₕ Q) xs
    ≡⟨ ·Homeval n 0ₕ Q _ ⟩
      eval n 0ₕ xs · eval n Q xs
    ≡⟨ cong (λ u → u · eval n Q xs) (eval0H _ xs) ⟩
      0 · eval n Q xs ∎

  ⋆Homeval n r 0H x xs =
    eval (ℕ.suc n) (r ⋆ 0H) (x ∷ xs)         ≡⟨ refl ⟩
    0                                       ≡⟨ 0≡m·0 (eval n r xs) ⟩
    eval n r xs · 0                         ≡⟨ refl ⟩
    eval n r xs · eval (ℕ.suc n) 0H (x ∷ xs) ∎
  ⋆Homeval n r (P ·X+ Q) x xs =
      eval (ℕ.suc n) (r ⋆ (P ·X+ Q)) (x ∷ xs)                    ≡⟨ refl ⟩
      eval (ℕ.suc n) ((r ⋆ P) ·X+ (r ·ₕ Q)) (x ∷ xs)              ≡⟨ refl ⟩
      (eval (ℕ.suc n) (r ⋆ P) (x ∷ xs)) · x + eval n (r ·ₕ Q) xs
    ≡⟨ cong (λ u → u · x + eval n (r ·ₕ Q) xs) (⋆Homeval n r P x xs) ⟩
      (eval n r xs · eval (ℕ.suc n) P (x ∷ xs)) · x + eval n (r ·ₕ Q) xs
    ≡⟨ cong (λ u → (eval n r xs · eval (ℕ.suc n) P (x ∷ xs)) · x + u) (·Homeval n r Q xs) ⟩
      (eval n r xs · eval (ℕ.suc n) P (x ∷ xs)) · x + eval n r xs · eval n Q xs
    ≡⟨ cong (λ u → u  + eval n r xs · eval n Q xs) (sym (·-assoc (eval n r xs) (eval (suc n) P (x ∷ xs)) x)) ⟩
      eval n r xs · (eval (ℕ.suc n) P (x ∷ xs) · x) + eval n r xs · eval n Q xs
    ≡⟨ ·-distribˡ (eval n r xs)  ((eval (ℕ.suc n) P (x ∷ xs) · x)) (eval n Q xs) ⟩
      eval n r xs · ((eval (ℕ.suc n) P (x ∷ xs) · x) + eval n Q xs)
    ≡⟨ refl ⟩
      eval n r xs · eval (ℕ.suc n) (P ·X+ Q) (x ∷ xs) ∎

  combineCases :
    (n : ℕ) (Q : IteratedHornerForms n) (P S : IteratedHornerForms (ℕ.suc n))
    (xs : Vec ℕ (ℕ.suc n))
    → eval (ℕ.suc n) ((P ·X+ Q) ·ₕ S) xs ≡ eval (ℕ.suc n) (((P ·ₕ S) ·X+ 0ₕ) +ₕ (Q ⋆ S)) xs
  combineCases n Q P S (x ∷ xs) with (P ·ₕ S)
  ... | 0H =
    eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)                ≡⟨ refl ⟩
    0 + eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)           ≡⟨ cong (λ u → u + eval _ (Q ⋆ S) (x ∷ xs)) lemma ⟩
    eval (ℕ.suc n) (0H ·X+ 0ₕ) (x ∷ xs)
    + eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)              ≡⟨ sym (+Homeval (ℕ.suc n)
                                                      (0H ·X+ 0ₕ) (Q ⋆ S) (x ∷ xs)) ⟩
    eval (ℕ.suc n) ((0H ·X+ 0ₕ) +ₕ (Q ⋆ S)) (x ∷ xs) ∎
    where lemma : 0 ≡ eval (ℕ.suc n) (0H ·X+ 0ₕ) (x ∷ xs)
          lemma = 0
                ≡⟨ refl ⟩
                  0 + 0
                ≡⟨ cong (λ u → u + 0) refl ⟩
                  0 · x + 0
                ≡⟨ cong (λ u → 0 · x + u) (sym (eval0H _ xs)) ⟩
                  0 · x + eval n 0ₕ xs
                ≡⟨ cong (λ u → u · x + eval n 0ₕ xs) (sym (eval0H _ (x ∷ xs))) ⟩
                  eval (ℕ.suc n) 0H (x ∷ xs) · x + eval n 0ₕ xs
                ≡⟨ refl ⟩
                  eval (ℕ.suc n) (0H ·X+ 0ₕ) (x ∷ xs) ∎
  ... | (_ ·X+ _) = refl

  ·Homeval .ℕ.zero (const x) (const y) [] = refl
  ·Homeval (ℕ.suc n) 0H Q xs =
    eval (ℕ.suc n) (0H ·ₕ Q) xs        ≡⟨ eval0H _ xs ⟩
    0                                 ≡⟨ refl ⟩
    0 · eval (ℕ.suc n) Q xs          ≡⟨ cong (λ u → u · eval _ Q xs) (sym (eval0H _ xs)) ⟩
    eval (ℕ.suc n) 0H xs · eval (ℕ.suc n) Q xs ∎
  ·Homeval (ℕ.suc n) (P ·X+ Q) S (x ∷ xs) =
      eval (ℕ.suc n) ((P ·X+ Q) ·ₕ S) (x ∷ xs)
    ≡⟨ combineCases n Q P S (x ∷ xs) ⟩
      eval (ℕ.suc n) (((P ·ₕ S) ·X+ 0ₕ) +ₕ (Q ⋆ S)) (x ∷ xs)
    ≡⟨ +Homeval (ℕ.suc n) ((P ·ₕ S) ·X+ 0ₕ) (Q ⋆ S) (x ∷ xs) ⟩
      eval (ℕ.suc n) ((P ·ₕ S) ·X+ 0ₕ) (x ∷ xs) + eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)
    ≡⟨ refl ⟩
      (eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x + eval n 0ₕ xs)
      + eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)
    ≡⟨ cong (λ u → u + eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs))
          ((eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x + eval n 0ₕ xs)
         ≡⟨ cong (λ u → eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x + u) (eval0H _ xs) ⟩
           (eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x + 0)
         ≡⟨ +-zero _ ⟩
           (eval (ℕ.suc n) (P ·ₕ S) (x ∷ xs) · x)
         ≡⟨ cong (λ u → u · x) (·Homeval (ℕ.suc n) P S (x ∷ xs)) ⟩
           ((eval (ℕ.suc n) P (x ∷ xs) · eval (ℕ.suc n) S (x ∷ xs)) · x)
         ≡⟨ sym (·-assoc (eval (ℕ.suc n) P (x ∷ xs)) (eval (ℕ.suc n) S (x ∷ xs)) x) ⟩
           (eval (ℕ.suc n) P (x ∷ xs) · (eval (ℕ.suc n) S (x ∷ xs) · x))
         ≡⟨ cong (λ u → eval (ℕ.suc n) P (x ∷ xs) · u) (·-comm _ x) ⟩
           (eval (ℕ.suc n) P (x ∷ xs) · (x · eval (ℕ.suc n) S (x ∷ xs)))
         ≡⟨ ·-assoc (eval (ℕ.suc n) P (x ∷ xs)) x (eval (ℕ.suc n) S (x ∷ xs)) ⟩
           (eval (ℕ.suc n) P (x ∷ xs) · x) · eval (ℕ.suc n) S (x ∷ xs)
          ∎) ⟩
      (eval (ℕ.suc n) P (x ∷ xs) · x) · eval (ℕ.suc n) S (x ∷ xs)
      + eval (ℕ.suc n) (Q ⋆ S) (x ∷ xs)
    ≡⟨ cong (λ u → (eval (ℕ.suc n) P (x ∷ xs) · x) · eval (ℕ.suc n) S (x ∷ xs) + u)
            (⋆Homeval n Q S x xs) ⟩
      (eval (ℕ.suc n) P (x ∷ xs) · x) · eval (ℕ.suc n) S (x ∷ xs)
      + eval n Q xs · eval (ℕ.suc n) S (x ∷ xs)
    ≡⟨ ·-distribʳ (eval (ℕ.suc n) P (x ∷ xs) · x) (eval n Q xs) (eval (ℕ.suc n) S (x ∷ xs)) ⟩
      ((eval (ℕ.suc n) P (x ∷ xs) · x) + eval n Q xs) · eval (ℕ.suc n) S (x ∷ xs)
    ≡⟨ refl ⟩
      eval (ℕ.suc n) (P ·X+ Q) (x ∷ xs) · eval (ℕ.suc n) S (x ∷ xs) ∎
