{-# OPTIONS --safe #-}
module Cubical.Tactics.NatSolver.Examples where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec.Base

open import Cubical.Tactics.NatSolver.NatExpression
open import Cubical.Tactics.NatSolver.HornerForms
open import Cubical.Tactics.NatSolver.Solver
open import Cubical.Tactics.NatSolver.Reflection

private
  variable
    ℓ : Level

module ReflectionSolving where
  _ : (x y : ℕ) → (x + y) · (x + y) ≡ x · x + 2 · x · y + y · y
  _ = solve

  {-
    If you want to use the solver in some more complex situation,
    you have to declare a helper variable (`useSolver` below) that
    is a term of a dependent function type as above:
  -}
  module _ (SomeType : Type ℓ-zero) where
    complexSolverApplication :
      (someStuff : SomeType) → (x y : ℕ) → (moreStuff : SomeType)
      → x + y ≡ y + x
    complexSolverApplication someStuff x y moreStuff = useSolver x y
                              where useSolver : (x y : ℕ) → x + y ≡ y + x
                                    useSolver = solve

module SolvingExplained where
  open EqualityToNormalform renaming (solve to natSolve)
  open IteratedHornerOperations hiding (X)

  ℕ[X₀,X₁] = IteratedHornerForms 2
  X₀ : ℕ[X₀,X₁]
  X₀ = Variable 2 (Fin.zero)

  X₁ : ℕ[X₀,X₁]
  X₁ = Variable 2 (suc Fin.zero)

  Two : ℕ[X₀,X₁]
  Two = Constant 2 2

  _ : eval X₀ (1 ∷ 0 ∷ []) ≡ 1
  _ = refl

  _ : eval X₁ (0 ∷ 1 ∷ []) ≡ 1
  _ = refl

  X : Expr 3
  X = ∣ Fin.zero

  Y : Expr 3
  Y = ∣ (suc Fin.zero)

  Z : Expr 3
  Z = ∣ (suc (suc Fin.zero))

  {-
     'normalize' maps an expression to its Horner Normalform.
     Two expressions evaluating to the same ring element
     have the same Horner Normal form.
     This means equality of the represented ring elements
     can be checked by agda's unification (so refl is a proof)

   -}
  _ : normalize ((K 2) ·' X) ≡
      normalize (X +' X)
  _ = refl


  _ : normalize ((K 2) ·' X) ≡ normalize (X +' X)
  _ = refl

  _ : normalize (((K 2) ·' X) ·' Y) ≡ normalize (Y ·' (X +' X))
  _ = refl

  _ : normalize (Z ·' (((K 2) ·' X) ·' Y)) ≡ normalize (Z ·' (Y ·' (X +' X)))
  _ = refl


  {-
    The solver needs to produce an equality between
    actual ring elements. So we need a proof that
    those actual ring elements are equal to a normal form:
  -}
  _ : (x y z : ℕ) →
      eval (normalize ((K 2) ·' X ·' Y)) (x ∷ y ∷ z ∷ [])
      ≡ 2 · x · y
  _ = λ x y z → isEqualToNormalform ((K 2) ·' X ·' Y) (x ∷ y ∷ z ∷ [])

  {-
    Now two of these proofs can be plugged together
    to solve an equation:
  -}
  open Eval
  _ : (x y z : ℕ) → 3 + x + y · y ≡ y · y + x + 1 + 2
  _ = let
        lhs = (K 3) +' X +' (Y ·' Y)
        rhs = Y ·' Y +' X +' (K 1) +' (K 2)
      in (λ x y z →
          ⟦ lhs ⟧ (x ∷ y ∷ z ∷ [])
        ≡⟨ sym (isEqualToNormalform lhs (x ∷ y ∷ z ∷ [])) ⟩
          eval (normalize lhs) (x ∷ y ∷ z ∷ [])
        ≡⟨ refl ⟩
          eval (normalize rhs) (x ∷ y ∷ z ∷ [])
        ≡⟨ isEqualToNormalform rhs (x ∷ y ∷ z ∷ []) ⟩
          ⟦ rhs ⟧ (x ∷ y ∷ z ∷ []) ∎)

  {-
    Parts of that can be automated easily:
  -}
  _ : (x y z : ℕ) → (x + y) · (x + y) ≡ x · x + 2 · x · y + y · y
  _ = λ x y z → let
              lhs = (X +' Y) ·' (X +' Y)
              rhs = X ·' X +' (K 2) ·' X ·' Y +' Y ·' Y
             in natSolve lhs rhs (x ∷ y ∷ z ∷ []) refl

  {-
    A bigger example
  -}
  _ : (x y z : ℕ) → (x + y) · (x + y) · (x + y) · (x + y)
                ≡ x · x · x · x + 4 · x · x · x · y + 6 · x · x · y · y
                  +  4 · x · y · y · y + y · y · y · y
  _ = λ x y z → let
              lhs = (X +' Y) ·' (X +' Y) ·' (X +' Y) ·' (X +' Y)
              rhs = X ·' X ·' X ·' X
                  +' (K 4) ·' X ·' X ·' X ·' Y
                  +' (K 6) ·' X ·' X ·' Y ·' Y
                  +' (K 4) ·' X ·' Y ·' Y ·' Y
                  +' Y ·' Y ·' Y ·' Y
             in natSolve lhs rhs (x ∷ y ∷ z ∷ []) refl
  {-
    this one cannot work so far:

  _ : (x y z : ℕ) → (x + y) · (x - y) ≡ (x · x - (y · y))
  _ = λ x y z → let
                lhs = (X +' Y) ·' (X +' (-' Y))
                rhs = (X ·' X) +' (-' (Y ·' Y))
              in natSolve lhs rhs (x ∷ y ∷ z ∷ []) {!!}
  -}
