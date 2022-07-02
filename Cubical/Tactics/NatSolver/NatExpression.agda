{-# OPTIONS --safe #-}
module Cubical.Tactics.NatSolver.NatExpression where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base

infixl 6 _+'_
infixl 7 _·'_

-- Expression in a ring on A with n variables
data Expr (n : ℕ) : Type ℓ-zero where
  K : ℕ → Expr n
  ∣ : Fin n → Expr n
  _+'_ : Expr n → Expr n → Expr n
  _·'_ : Expr n → Expr n → Expr n

module Eval where
  open import Cubical.Data.Vec

  ⟦_⟧ : ∀ {n} → Expr n → Vec ℕ n → ℕ
  ⟦ K r ⟧ v = r
  ⟦ ∣ k ⟧ v = lookup k v
  ⟦ x +' y ⟧ v =  ⟦ x ⟧ v + ⟦ y ⟧ v
  ⟦ x ·' y ⟧ v = ⟦ x ⟧ v · ⟦ y ⟧ v
