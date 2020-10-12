{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.Examples where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Vec.Base

open import Cubical.Algebra.RingSolver.AlmostRing
open import Cubical.Algebra.RingSolver.NatAsAlmostRing
open import Cubical.Algebra.RingSolver.RingExpression
open import Cubical.Algebra.RingSolver.RawRing renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Algebra.RingSolver.HornerNormalForm
open import Cubical.Algebra.RingSolver.MultivariatePolynomials
open import Cubical.Algebra.RingSolver.Solver

module RingSolvingInOneVariable where
  open AlmostRing ℕAsAlmostRing
  open HornerOperations (AlmostRing→RawRing ℕAsAlmostRing)
  open Eval (AlmostRing→RawRing ℕAsAlmostRing)
  open SolverFor ℕAsAlmostRing

  ExprX : Expr ℕ 1
  ExprX = ∣ (fromℕ 0)

  {-
     Reify maps an expression to its Horner Normalform.
     Two expressions evaluating to the same ring element
     have the same Horner Normal form.
     This means equality of the represented ring elements
     can be checked by agda's unification (so refl is a proof)
   -}
  _ : Reify ((K 2) ⊗ ExprX) ≡
      Reify (ExprX ⊕ ExprX)
  _ = refl

  _ : Reify (ExprX ⊕ (K (1 + 1))) ≡
      Reify ((K 0) ⊗ ExprX ⊕ (K 1) ⊗ (K 2) ⊕ ExprX)
  _ = refl

  {-
    The solver needs to produce an equality between
    actual ring elements. So we need a proof that
    those actual ring elements are equal to a normal form:
  -}
  _ : (x : ℕ) → evalH (Reify ((K 2) ⊗ ExprX)) x ≡ 2 · x
  _ = isEqualToNormalForm ((K 2) ⊗ ExprX)

  {-
    Now two of these proofs can be plugged together
    to solve an equation:
  -}
  _ : (x : ℕ) → 3 + x + x ≡ 1 + 2 · x + 1 + 1
  _ = let
        lhs = (K 3) ⊕ ExprX ⊕ ExprX
        rhs = (K 1) ⊕ (K 2) ⊗ ExprX ⊕ (K 1) ⊕ (K 1)
      in (λ x →   ⟦ lhs ⟧ (x ∷ [])    ≡⟨ sym (isEqualToNormalForm lhs x) ⟩
                  evalH (Reify lhs) x ≡⟨ refl ⟩
                  evalH (Reify rhs) x ≡⟨ isEqualToNormalForm rhs x ⟩
                  ⟦ rhs ⟧ (x ∷ [])    ∎)
  {-
    Parts of that can be automated easily:
  -}
  _ : (x : ℕ) → 3 + x + x ≡ 1 + 2 · x + 1 + 1
  _ = λ x → let
              lhs = (K 3) ⊕ ExprX ⊕ ExprX
              rhs = (K 1) ⊕ (K 2) ⊗ ExprX ⊕ (K 1) ⊕ (K 1)
             in SolveExplicit lhs rhs x refl

  _ : (x : ℕ) → (x + 2) · (x + x) ≡ 2 · x · x + 4 · x
  _ = λ x → let
              lhs = (ExprX ⊕ (K 2)) ⊗ (ExprX ⊕ ExprX)
              rhs = ((K 2) ⊗ ExprX ⊗ ExprX) ⊕ ((K 4) ⊗ ExprX)
             in SolveExplicit lhs rhs x refl

  _ : (x : ℕ) → (x + 2) · (x + x) · (x · x + x + 1) ≡
                2 · x · x · x · x + 6 · x · x · x + 6 · x · x + 4 · x
  _ = λ x → let
              lhs = (ExprX ⊕ (K 2)) ⊗ (ExprX ⊕ ExprX)
                    ⊗ (ExprX ⊗ ExprX ⊕ ExprX ⊕ (K 1))
              rhs = ((K 2) ⊗ ExprX ⊗ ExprX ⊗ ExprX ⊗ ExprX)
                  ⊕ ((K 6) ⊗ ExprX ⊗ ExprX ⊗ ExprX)
                  ⊕ ((K 6) ⊗ ExprX ⊗ ExprX)
                  ⊕ ((K 4) ⊗ ExprX)
             in SolveExplicit lhs rhs x refl

  {-
     This one could take some time to check if it did
     but somehow it doesn't...
  -}
  _ : (x : ℕ) → (x + x) · (x + x) · (x + x)
              · (x + x) · (x + x) · (x + x)
              · (x + x) · (x + x) · (x + x)
              · (x + x) · (x + x) · (x + x)
              ≡ 4096 · x · x · x
                     · x · x · x
                     · x · x · x
                     · x · x · x
  _ = λ x → let
              lhs = (ExprX ⊕ ExprX)
                  ⊗ (ExprX ⊕ ExprX)
                  ⊗ (ExprX ⊕ ExprX)
                  ⊗ (ExprX ⊕ ExprX)
                  ⊗ (ExprX ⊕ ExprX)
                  ⊗ (ExprX ⊕ ExprX)
                  ⊗ (ExprX ⊕ ExprX)
                  ⊗ (ExprX ⊕ ExprX)
                  ⊗ (ExprX ⊕ ExprX)
                  ⊗ (ExprX ⊕ ExprX)
                  ⊗ (ExprX ⊕ ExprX)
                  ⊗ (ExprX ⊕ ExprX)
              rhs = ((K 4096) ⊗ ExprX ⊗ ExprX ⊗ ExprX
                              ⊗ ExprX ⊗ ExprX ⊗ ExprX
                              ⊗ ExprX ⊗ ExprX ⊗ ExprX
                              ⊗ ExprX ⊗ ExprX ⊗ ExprX)
             in SolveExplicit lhs rhs x refl

module Multivariate where
  ℕAsRawRing = AlmostRing→RawRing ℕAsAlmostRing

  ℕ[X₀,X₁] = IteratedHornerForms 2 ℕAsRawRing
  open RawRing ℕ[X₀,X₁]

  X₀ : ⟨ ℕ[X₀,X₁] ⟩ᵣ
  X₀ = Variable 2 ℕAsRawRing (Fin.zero)

  X₁ : ⟨ ℕ[X₀,X₁] ⟩ᵣ
  X₁ = Variable 2 ℕAsRawRing (fromℕ 1)

  Two : ⟨ ℕ[X₀,X₁] ⟩ᵣ
  Two = Constant 2 ℕAsRawRing 2

  _ : Evaluate X₀ (1 ∷ 0 ∷ []) ≡ 1
  _ = refl

  _ : Evaluate X₁ (0 ∷ 1 ∷ []) ≡ 1
  _ = refl

  _ : Evaluate (X₀ · X₁ + X₀ + X₁ · X₁ + Two) (2 ∷ 3 ∷ []) ≡ 19
  _ = refl
