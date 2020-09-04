{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.RingExpression where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (zero-≤)

open import Cubical.Algebra.RingSolver.AlmostRing

private
  variable
    ℓ : Level

infixl 6 _⊕_
infixl 7 _⊗_
infixr 8 _⊛_

-- Expression in an almost ring on A with n variables
data Expr {ℓ} (A : Type ℓ) (n : ℕ) : Type ℓ where
  K : A → Expr A n
  ∣ : Fin n → Expr A n
  _⊕_ : Expr A n → Expr A n → Expr A n
  _⊗_ : Expr A n → Expr A n → Expr A n
--  _⊛_ : Expr A n → ℕ → Expr A n    -- exponentiation
  ⊝_ : Expr A n → Expr A n

-- there are probably things I don't get yet...
module Eval (R : AlmostRing {ℓ}) where
  open import Cubical.Data.Vec
  open AlmostRing R

  ⟦_⟧ : ∀ {n} → Expr ⟨ R ⟩ n → Vec ⟨ R ⟩ n → ⟨ R ⟩
  ⟦ K r ⟧ v = r
  ⟦ ∣ k ⟧ v = lookup k v
  ⟦ x ⊕ y ⟧ v =  ⟦ x ⟧ v + ⟦ y ⟧ v
  ⟦ x ⊗ y ⟧ v = ⟦ x ⟧ v · ⟦ y ⟧ v
--  ⟦ x ⊛ l ⟧ v =  ⟦ x ⟧ v ^ l
  ⟦ ⊝ x ⟧ v = - ⟦ x ⟧ v

data RawHornerPolynomial (R : AlmostRing {ℓ}) : Type ℓ where
  0H : RawHornerPolynomial R
  _·X+_ : RawHornerPolynomial R → ⟨ R ⟩ → RawHornerPolynomial R


module Horner (R : AlmostRing {ℓ}) where
  open AlmostRing R

  1H : RawHornerPolynomial R
  1H = 0H ·X+ 1r

  X : RawHornerPolynomial R
  X = 1H ·X+ 0r

  _+H_ : RawHornerPolynomial R → RawHornerPolynomial R → RawHornerPolynomial R
  0H +H Q = Q
  (P ·X+ r) +H 0H = P ·X+ r
  (P ·X+ r) +H (Q ·X+ s) = (P +H Q) ·X+ (r + s)

  _⋆_ : ⟨ R ⟩ → RawHornerPolynomial R → RawHornerPolynomial R
  r ⋆ 0H = 0H
  r ⋆ (P ·X+ s) = (r ⋆ P) ·X+ (s · r)

  _·H_ : RawHornerPolynomial R → RawHornerPolynomial R → RawHornerPolynomial R
  0H ·H _ = 0H
  (P ·X+ r) ·H Q = (P ·H Q) +H (r ⋆ Q)

  -H_ : RawHornerPolynomial R → RawHornerPolynomial R
  -H 0H = 0H
  -H (P ·X+ r) = (-H P) ·X+ (- r)

module Normalize (R : AlmostRing {ℓ}) where
  open AlmostRing R
  open Horner R

  ⟦_⇓⟧ : Expr ⟨ R ⟩ 1 → RawHornerPolynomial R
  ⟦ K r ⇓⟧ = 0H ·X+ 0r
  ⟦ ∣ k ⇓⟧ = X
  ⟦ x ⊕ y ⇓⟧ = ⟦ x ⇓⟧ +H ⟦ y ⇓⟧
  ⟦ x ⊗ y ⇓⟧ = ⟦ x ⇓⟧ ·H ⟦ y ⇓⟧
  ⟦ ⊝ x ⇓⟧ =  -H ⟦ x ⇓⟧
