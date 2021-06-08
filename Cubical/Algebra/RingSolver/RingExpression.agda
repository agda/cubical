{-# OPTIONS --safe #-}
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

-- Expression in a ring on A with n variables
data Expr {ℓ} (A : Type ℓ) (n : ℕ) : Type ℓ where
  K : A → Expr A n
  ∣ : Fin n → Expr A n
  _⊕_ : Expr A n → Expr A n → Expr A n
  _⊗_ : Expr A n → Expr A n → Expr A n
--  _⊛_ : Expr A n → ℕ → Expr A n    -- exponentiation
  ⊝_ : Expr A n → Expr A n

module Eval (R : RawRing ℓ) where
  open import Cubical.Data.Vec
  open RawRing R

  ⟦_⟧ : ∀ {n} → Expr ⟨ R ⟩ᵣ n → Vec ⟨ R ⟩ᵣ n → ⟨ R ⟩ᵣ
  ⟦ K r ⟧ v = r
  ⟦ ∣ k ⟧ v = lookup k v
  ⟦ x ⊕ y ⟧ v =  ⟦ x ⟧ v + ⟦ y ⟧ v
  ⟦ x ⊗ y ⟧ v = ⟦ x ⟧ v · ⟦ y ⟧ v
--  ⟦ x ⊛ l ⟧ v =  ⟦ x ⟧ v ^ l
  ⟦ ⊝ x ⟧ v = - ⟦ x ⟧ v
