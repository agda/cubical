{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.CommRingHornerEval where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int hiding (_+_ ; _·_ ; -_)
open import Cubical.Data.Vec
open import Cubical.Data.Bool
open import Cubical.Data.Empty hiding () renaming (rec to recEmpty)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.RingSolver.RawAlgebra
open import Cubical.Algebra.RingSolver.IntAsRawRing
open import Cubical.Algebra.RingSolver.CommRingHornerForms
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

private
  variable
    ℓ ℓ′ : Level

eval : {A : RawAlgebra ℤAsRawRing ℓ′}
       (n : ℕ) (P : IteratedHornerForms A n)
       → Vec ⟨ A ⟩ n → ⟨ A ⟩
eval {A = A} ℕ.zero (const r) [] = RawAlgebra.scalar A r
eval {A = A} .(ℕ.suc _) 0H (_ ∷ _) = RawAlgebra.0r A
eval {A = A} (ℕ.suc n) (P ·X+ Q) (x ∷ xs) =
     let open RawAlgebra A
         P' = (eval (ℕ.suc n) P (x ∷ xs))
         Q' = eval n Q xs
     in if (isZero A P)
        then Q'
        else P' · x + Q'

module _ (R : CommRing ℓ) where
  private
    νR = CommRing→RawℤAlgebra R
  open CommRingStr (snd R)
  open RingTheory (CommRing→Ring R)

  private
    byAbsurdity : {Anything : Type ℓ′} → false ≡ true → Anything
    byAbsurdity p = recEmpty (false≢true p)

    extract : (P Q : Bool)
                  → P and Q ≡ true
                  → (P ≡ true) × (Q ≡ true)
    extract false false eq = byAbsurdity eq
    extract false true eq = byAbsurdity eq
    extract true false eq = byAbsurdity eq
    extract true true eq = eq , eq

  evalIsZero : {n : ℕ} (P : IteratedHornerForms νR n)
             → (l : Vec ⟨ νR ⟩ n)
             → isZero νR P ≡ true
             → eval n P l ≡ 0r
  evalIsZero (const (pos ℕ.zero)) [] isZeroP = refl
  evalIsZero (const (pos (ℕ.suc n))) [] isZeroP = byAbsurdity isZeroP
  evalIsZero (const (negsuc _)) [] isZeroP = byAbsurdity isZeroP
  evalIsZero 0H (x ∷ xs) _ = refl
  evalIsZero {n = ℕ.suc n} (P ·X+ Q) (x ∷ xs) isZeroPandQ with isZero νR P
  ... | true = eval n Q xs   ≡⟨ evalIsZero Q xs isZeroQ ⟩
               0r ∎
               where isZeroQ = snd (extract _ _ isZeroPandQ)
  ... | false = byAbsurdity isZeroP
               where isZeroP = fst (extract _ _ isZeroPandQ)

  computeEvalIsZero :
               {n : ℕ}
               (P : IteratedHornerForms νR (ℕ.suc n))
               (Q : IteratedHornerForms νR n)
             → (xs : Vec ⟨ νR ⟩ n)
             → (x : ⟨ νR ⟩)
             → isZero νR P ≡ true
             → eval _ (P ·X+ Q) (x ∷ xs) ≡ eval n Q xs
  computeEvalIsZero P Q xs x isZeroP with isZero νR P
  ... | true = refl
  ... | false = byAbsurdity isZeroP

  computeEvalNotZero :
               {n : ℕ}
               (P : IteratedHornerForms νR (ℕ.suc n))
               (Q : IteratedHornerForms νR n)
             → (xs : Vec ⟨ νR ⟩ n)
             → (x : ⟨ νR ⟩)
             → ¬ (isZero νR P ≡ true)
             → eval _ (P ·X+ Q) (x ∷ xs) ≡ (eval _ P (x ∷ xs)) · x + eval n Q xs
  computeEvalNotZero P Q xs x notZeroP with isZero νR P
  ... | true = byAbsurdity (sym (¬true→false true notZeroP))
  ... | false = refl

  combineCasesEval :
    {n : ℕ}  (P : IteratedHornerForms νR (ℕ.suc n)) (Q : IteratedHornerForms νR n)
    (x : (fst R)) (xs : Vec ⟨ νR ⟩ n)
    →   eval _ (P ·X+ Q) (x ∷ xs)
      ≡ (eval _ P (x ∷ xs)) · x + eval n Q xs
  combineCasesEval P Q x xs with isZero νR P  ≟ true
  ... | yes p =
       eval _ (P ·X+ Q) (x ∷ xs)            ≡⟨ computeEvalIsZero P Q xs x p ⟩
       eval _ Q xs                          ≡⟨ sym (+Lid _) ⟩
       0r + eval _ Q xs                     ≡[ i ]⟨ 0LeftAnnihilates x (~ i) + eval _ Q xs ⟩
       0r · x + eval _ Q xs                 ≡[ i ]⟨ (evalIsZero P (x ∷ xs) p (~ i)) · x + eval _ Q xs ⟩
       (eval _ P (x ∷ xs)) · x + eval _ Q xs ∎
  ... | no p  = computeEvalNotZero P Q xs x p

