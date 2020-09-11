{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.RingExpression where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
open import Cubical.Algebra.RingSolver.AlmostRing
open import Cubical.Algebra.RingSolver.RawRing renaming (⟨_⟩ to ⟨_⟩ᵣ)

private
  variable
    ℓ : Level

infixl 6 _⊕_
infixl 7 _⊗_

-- Expression in an almost ring on A with n variables
data Expr {ℓ} (A : Type ℓ) (n : ℕ) : Type ℓ where
  K : A → Expr A n
  ∣ : Fin n → Expr A n
  _⊕_ : Expr A n → Expr A n → Expr A n
  _⊗_ : Expr A n → Expr A n → Expr A n
--  _⊛_ : Expr A n → ℕ → Expr A n    -- exponentiation
  ⊝_ : Expr A n → Expr A n

-- there are probably things I don't get yet...
module Eval (R : RawRing {ℓ}) where
  open import Cubical.Data.Vec
  open RawRing R

  ⟦_⟧ : ∀ {n} → Expr ⟨ R ⟩ᵣ n → Vec ⟨ R ⟩ᵣ n → ⟨ R ⟩ᵣ
  ⟦ K r ⟧ v = r
  ⟦ ∣ k ⟧ v = lookup k v
  ⟦ x ⊕ y ⟧ v =  ⟦ x ⟧ v + ⟦ y ⟧ v
  ⟦ x ⊗ y ⟧ v = ⟦ x ⟧ v · ⟦ y ⟧ v
--  ⟦ x ⊛ l ⟧ v =  ⟦ x ⟧ v ^ l
  ⟦ ⊝ x ⟧ v = - ⟦ x ⟧ v

data RawHornerPolynomial (R : RawRing {ℓ}) : Type ℓ where
  0H : RawHornerPolynomial R
  _·X+_ : RawHornerPolynomial R → ⟨ R ⟩ᵣ → RawHornerPolynomial R


module Horner (R : RawRing {ℓ}) where
  open RawRing R

  1H : RawHornerPolynomial R
  1H = 0H ·X+ 1r

  X : RawHornerPolynomial R
  X = 1H ·X+ 0r

  _+H_ : RawHornerPolynomial R → RawHornerPolynomial R → RawHornerPolynomial R
  0H +H Q = Q
  (P ·X+ r) +H 0H = P ·X+ r
  (P ·X+ r) +H (Q ·X+ s) = (P +H Q) ·X+ (r + s)

  _⋆_ : ⟨ R ⟩ᵣ → RawHornerPolynomial R → RawHornerPolynomial R
  r ⋆ 0H = 0H
  r ⋆ (P ·X+ s) = (r ⋆ P) ·X+ (s · r)

  _·H_ : RawHornerPolynomial R → RawHornerPolynomial R → RawHornerPolynomial R
  0H ·H _ = 0H
  (P ·X+ r) ·H Q = (P ·H Q) +H (r ⋆ Q)

  -H_ : RawHornerPolynomial R → RawHornerPolynomial R
  -H 0H = 0H
  -H (P ·X+ r) = (-H P) ·X+ (- r)

  evalH : RawHornerPolynomial R → ⟨ R ⟩ᵣ → ⟨ R ⟩ᵣ
  evalH 0H x₀ = 0r
  evalH (P ·X+ r) x₀ = (evalH P x₀) · x₀ + r

module Normalize (R : AlmostRing {ℓ}) where
  νR = AlmostRing→RawRing R
  open AlmostRing R
  open Theory R
  open Horner νR
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

  Reify : Expr ⟨ R ⟩ 1 → RawHornerPolynomial νR
  Reify (K r) = 0H ·X+ r
  Reify (∣ k) = X
  Reify (x ⊕ y) = (Reify x) +H (Reify y)
  Reify (x ⊗ y) = (Reify x) ·H (Reify y)
  Reify (⊝ x) =  -H (Reify x)
