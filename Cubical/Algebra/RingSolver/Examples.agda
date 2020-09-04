{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.RingSolver.AlmostRing
open import Cubical.Algebra.RingSolver.NatAsAlmostRing
open import Cubical.Algebra.RingSolver.RingExpression
open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)


module _ where
  open AlmostRing ℕAsAlmostRing
  open Normalize ℕAsAlmostRing
  open Horner ℕAsAlmostRing

  ExprX : Expr ℕ 1
  ExprX = ∣ (fromℕ 0)

  _ : Reify ((K 2) ⊗ ExprX) ≡
      Reify (ExprX ⊕ ExprX)
  _ = refl

  _ : Reify (ExprX ⊕ (K (1 + 1))) ≡
      Reify ((K 0) ⊗ ExprX ⊕ (K 1) ⊗ (K 2) ⊕ ExprX)
  _ = refl
