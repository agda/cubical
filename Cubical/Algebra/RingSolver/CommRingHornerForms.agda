{-# OPTIONS --safe #-}
module Cubical.Algebra.RingSolver.CommRingHornerForms where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int hiding (_+_ ; _·_ ; -_)
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_; _and_; false≢true; ¬true→false)
open import Cubical.Data.Empty hiding () renaming (rec to recEmpty)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary.Base using (¬_)

open import Cubical.Algebra.RingSolver.RawRing
open import Cubical.Algebra.RingSolver.IntAsRawRing
open import Cubical.Algebra.RingSolver.RawAlgebra renaming (⟨_⟩ to ⟨_⟩ₐ)
open import Cubical.Algebra.RingSolver.AlgebraExpression public
open import Cubical.Algebra.CommRing

private
  variable
    ℓ ℓ′ : Level

{-
  This defines the type of multivariate Polynomials over the RawRing R.
  The construction is based on the algebraic fact

    R[X₀][X₁]⋯[Xₙ] ≅ R[X₀,⋯,Xₙ]

  BUT: Contrary to algebraic convetions, we will give 'Xₙ' the lowest index
  in the definition of 'Variable' below. So if 'Variable n R k' is identified
  with 'Xₖ', then the RawRing we construct should rather be denoted with

    R[Xₙ][Xₙ₋₁]⋯[X₀]

  or, to be precise about the evaluation order:

    (⋯((R[Xₙ])[Xₙ₋₁])⋯)[X₀]

-}

data IteratedHornerForms (A : RawAlgebra ℤAsRawRing ℓ) : ℕ → Type ℓ where
  const : ℤ → IteratedHornerForms A ℕ.zero
  0H : {n : ℕ} → IteratedHornerForms A (ℕ.suc n)
  _·X+_ : {n : ℕ} → IteratedHornerForms A (ℕ.suc n) → IteratedHornerForms A n
                  → IteratedHornerForms A (ℕ.suc n)


{-
  The following function returns true, if there is some
  obvious reason that the Horner-Expression should be zero.
  Since Equality is undecidable in a general RawAlgebra, we cannot
  have a function that fully lives up to the name 'isZero'.
-}
module _ (A : RawAlgebra ℤAsRawRing ℓ′) where
  open RawRing ℤAsRawRing
  isZero : {n : ℕ} → IteratedHornerForms A n
                   → Bool
  isZero (const (pos ℕ.zero)) = true
  isZero (const (pos (ℕ.suc _))) = false
  isZero (const (negsuc _)) = false
  isZero 0H = true
  isZero (P ·X+ Q) = (isZero P) and (isZero Q)

eval : {A : RawAlgebra ℤAsRawRing ℓ′}
       (n : ℕ) (P : IteratedHornerForms A n)
       → Vec ⟨ A ⟩ₐ n → ⟨ A ⟩ₐ
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
             → (l : Vec ⟨ νR ⟩ₐ n)
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
             → (xs : Vec ⟨ νR ⟩ₐ n)
             → (x : ⟨ νR ⟩ₐ)
             → isZero νR P ≡ true
             → eval _ (P ·X+ Q) (x ∷ xs) ≡ eval n Q xs
  computeEvalIsZero P Q xs x isZeroP with isZero νR P
  ... | true = refl
  ... | false = byAbsurdity isZeroP

  computeEvalNotZero :
               {n : ℕ}
               (P : IteratedHornerForms νR (ℕ.suc n))
               (Q : IteratedHornerForms νR n)
             → (xs : Vec ⟨ νR ⟩ₐ n)
             → (x : ⟨ νR ⟩ₐ)
             → ¬ (isZero νR P ≡ true)
             → eval _ (P ·X+ Q) (x ∷ xs) ≡ (eval _ P (x ∷ xs)) · x + eval n Q xs
  computeEvalNotZero P Q xs x notZeroP with isZero νR P
  ... | true = byAbsurdity (sym (¬true→false true notZeroP))
  ... | false = refl

module IteratedHornerOperations (A : RawAlgebra ℤAsRawRing ℓ) where
  open RawRing ℤAsRawRing

  private
    1H' : (n : ℕ) → IteratedHornerForms A n
    1H' ℕ.zero = const 1r
    1H' (ℕ.suc n) = 0H ·X+ 1H' n

    0H' : (n : ℕ) → IteratedHornerForms A n
    0H' ℕ.zero = const 0r
    0H' (ℕ.suc n) = 0H

  1ₕ : {n : ℕ} → IteratedHornerForms A n
  1ₕ {n = n} = 1H' n

  0ₕ : {n : ℕ} → IteratedHornerForms A n
  0ₕ {n = n} = 0H' n

  X : (n : ℕ) (k : Fin n) → IteratedHornerForms A n
  X (ℕ.suc m) zero = 1ₕ ·X+ 0ₕ
  X (ℕ.suc m) (suc k) = 0ₕ ·X+ X m k

  _+ₕ_ : {n : ℕ} → IteratedHornerForms A n → IteratedHornerForms A n
               → IteratedHornerForms A n
  (const r) +ₕ (const s) = const (r + s)
  0H +ₕ Q = Q
  (P ·X+ r) +ₕ 0H = P ·X+ r
  (P ·X+ r) +ₕ (Q ·X+ s) =
    let left = (P +ₕ Q)
        right = (r +ₕ s)
    in if ((isZero A left) and (isZero A right))
       then 0ₕ
       else left ·X+ right

  -ₕ : {n : ℕ} → IteratedHornerForms A n → IteratedHornerForms A n
  -ₕ (const x) = const (- x)
  -ₕ 0H = 0H
  -ₕ (P ·X+ Q) = (-ₕ P) ·X+ (-ₕ Q)

  _⋆_ : {n : ℕ} → IteratedHornerForms A n → IteratedHornerForms A (ℕ.suc n)
                → IteratedHornerForms A (ℕ.suc n)
  _·ₕ_ : {n : ℕ} → IteratedHornerForms A n → IteratedHornerForms A n
                → IteratedHornerForms A n
  r ⋆ 0H = 0H
  r ⋆ (P ·X+ Q) =
    if (isZero A r)
    then 0ₕ
    else (r ⋆ P) ·X+ (r ·ₕ Q)

  const x ·ₕ const y = const (x · y)
  0H ·ₕ Q = 0H
  (P ·X+ Q) ·ₕ S =
     let
        z = (P ·ₕ S)
     in if (isZero A z)
        then (Q ⋆ S)
        else (z ·X+ 0ₕ) +ₕ (Q ⋆ S)

  asRawRing : (n : ℕ) → RawRing ℓ
  RawRing.Carrier (asRawRing n) = IteratedHornerForms A n
  RawRing.0r (asRawRing n) = 0ₕ
  RawRing.1r (asRawRing n) = 1ₕ
  RawRing._+_ (asRawRing n) = _+ₕ_
  RawRing._·_ (asRawRing n) = _·ₕ_
  RawRing.- (asRawRing n) =  -ₕ

Variable : (n : ℕ) (R : RawAlgebra ℤAsRawRing ℓ′) (k : Fin n) → IteratedHornerForms R n
Variable n R k = IteratedHornerOperations.X R n k

Constant : (n : ℕ) (R : RawAlgebra ℤAsRawRing ℓ′) (r : ℤ) → IteratedHornerForms R n
Constant ℕ.zero R r = const r
Constant (ℕ.suc n) R r = IteratedHornerOperations.0ₕ R ·X+ Constant n R r
