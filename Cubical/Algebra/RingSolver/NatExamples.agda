{-# OPTIONS --safe #-}
module Cubical.Algebra.RingSolver.NatExamples where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Vec.Base

open import Cubical.Algebra.RingSolver.AlmostRing
open import Cubical.Algebra.RingSolver.NatAsAlmostRing
open import Cubical.Algebra.RingSolver.RingExpression
open import Cubical.Algebra.RingSolver.RawRing renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Algebra.RingSolver.HornerForms
open import Cubical.Algebra.RingSolver.Solver

private
  variable
    ℓ : Level

module MultivariateSolving where
  open AlmostRing ℕAsAlmostRing
  ℕAsRawRing = AlmostRing→RawRing ℕAsAlmostRing
  open EqualityToNormalform ℕAsAlmostRing
  ℕ[X₀,X₁] = IteratedHornerOperations.asRawRing ℕAsRawRing 2

  X₀ : ⟨ ℕ[X₀,X₁] ⟩ᵣ
  X₀ = Variable 2 ℕAsRawRing (Fin.zero)

  X₁ : ⟨ ℕ[X₀,X₁] ⟩ᵣ
  X₁ = Variable 2 ℕAsRawRing (suc Fin.zero)

  Two : ⟨ ℕ[X₀,X₁] ⟩ᵣ
  Two = Constant 2 ℕAsRawRing 2

  _ : eval 2 X₀ (1 ∷ 0 ∷ []) ≡ 1
  _ = refl

  _ : eval 2 X₁ (0 ∷ 1 ∷ []) ≡ 1
  _ = refl

  X : Expr ℕ 3
  X = ∣ Fin.zero

  Y : Expr ℕ 3
  Y = ∣ (suc Fin.zero)

  Z : Expr ℕ 3
  Z = ∣ (suc (suc Fin.zero))

  {-
     'normalize' maps an expression to its Horner Normalform.
     Two expressions evaluating to the same ring element
     have the same Horner Normal form.
     This means equality of the represented ring elements
     can be checked by agda's unification (so refl is a proof)

   -}
  _ : normalize 3 ((K 2) ⊗ X) ≡
      normalize 3 (X ⊕ X)
  _ = refl


  _ : normalize 3 ((K 2) ⊗ X) ≡ normalize 3 (X ⊕ X)
  _ = refl

  _ : normalize 3 (((K 2) ⊗ X) ⊗ Y) ≡ normalize 3 (Y ⊗ (X ⊕ X))
  _ = refl

  _ : normalize 3 (Z ⊗ (((K 2) ⊗ X) ⊗ Y)) ≡ normalize 3 (Z ⊗ (Y ⊗ (X ⊕ X)))
  _ = refl


  {-
    The solver needs to produce an equality between
    actual ring elements. So we need a proof that
    those actual ring elements are equal to a normal form:
  -}
  _ : (x y z : ℕ) →
      eval 3 (normalize 3 ((K 2) ⊗ X ⊗ Y)) (x ∷ y ∷ z ∷ [])
      ≡ 2 · x · y
  _ = λ x y z → isEqualToNormalform 3 ((K 2) ⊗ X ⊗ Y) (x ∷ y ∷ z ∷ [])

  {-
    Now two of these proofs can be plugged together
    to solve an equation:
  -}
  open Eval ℕAsRawRing
  _ : (x y z : ℕ) → 3 + x + y · y ≡ y · y + x + 1 + 2
  _ = let
        lhs = (K 3) ⊕ X ⊕ (Y ⊗ Y)
        rhs = Y ⊗ Y ⊕ X ⊕ (K 1) ⊕ (K 2)
      in (λ x y z →
          ⟦ lhs ⟧ (x ∷ y ∷ z ∷ [])
        ≡⟨ sym (isEqualToNormalform 3 lhs (x ∷ y ∷ z ∷ [])) ⟩
          eval 3 (normalize 3 lhs) (x ∷ y ∷ z ∷ [])
        ≡⟨ refl ⟩
          eval 3 (normalize 3 rhs) (x ∷ y ∷ z ∷ [])
        ≡⟨ isEqualToNormalform 3 rhs (x ∷ y ∷ z ∷ []) ⟩
          ⟦ rhs ⟧ (x ∷ y ∷ z ∷ []) ∎)

  {-
    Parts of that can be automated easily:
  -}
  _ : (x y z : ℕ) → (x + y) · (x + y) ≡ x · x + 2 · x · y + y · y
  _ = λ x y z → let
              lhs = (X ⊕ Y) ⊗ (X ⊕ Y)
              rhs = X ⊗ X ⊕ (K 2) ⊗ X ⊗ Y ⊕ Y ⊗ Y
             in solve lhs rhs (x ∷ y ∷ z ∷ []) refl

  {-
    A bigger example
  -}
  _ : (x y z : ℕ) → (x + y) · (x + y) · (x + y) · (x + y)
                ≡ x · x · x · x + 4 · x · x · x · y + 6 · x · x · y · y
                  +  4 · x · y · y · y + y · y · y · y
  _ = λ x y z → let
              lhs = (X ⊕ Y) ⊗ (X ⊕ Y) ⊗ (X ⊕ Y) ⊗ (X ⊕ Y)
              rhs = X ⊗ X ⊗ X ⊗ X
                  ⊕ (K 4) ⊗ X ⊗ X ⊗ X ⊗ Y
                  ⊕ (K 6) ⊗ X ⊗ X ⊗ Y ⊗ Y
                  ⊕ (K 4) ⊗ X ⊗ Y ⊗ Y ⊗ Y
                  ⊕ Y ⊗ Y ⊗ Y ⊗ Y
             in solve lhs rhs (x ∷ y ∷ z ∷ []) refl
  {-
    this one cannot work so far:

  _ : (x y z : ℕ) → (x + y) · (x - y) ≡ (x · x - (y · y))
  _ = λ x y z → let
                lhs = (X ⊕ Y) ⊗ (X ⊕ (⊝ Y))
                rhs = (X ⊗ X) ⊕ (⊝ (Y ⊗ Y))
              in solve lhs rhs (x ∷ y ∷ z ∷ []) {!!}
  -}

module ExamplesForArbitraryRings (R : AlmostRing ℓ) where
  open AlmostRing R
  open EqualityToNormalform R

  X : Expr ⟨ R ⟩ 4
  X = ∣ Fin.zero

  Y : Expr ⟨ R ⟩ 4
  Y = ∣ (suc Fin.zero)

  A : Expr ⟨ R ⟩ 4
  A = ∣ (suc (suc Fin.zero))

  B : Expr ⟨ R ⟩ 4
  B = ∣ (suc (suc (suc Fin.zero)))

  _ : (x y a b : ⟨ R ⟩) → (x + y) + (a + b) ≡ (y + b) + (x + a)
  _ = λ x y a b → let
                lhs = (X ⊕ Y) ⊕ (A ⊕ B)
                rhs = (Y ⊕ B) ⊕ (X ⊕ A)
              in solve lhs rhs (x ∷ y ∷ a ∷ b ∷ []) refl

  _ : (x y a b : ⟨ R ⟩) → (x + y) · (x + y) ≡ x · x + x · y + x · y + y · y
  _ = λ x y a b →
              let
                lhs = (X ⊕ Y) ⊗ (X ⊕ Y)
                rhs = (X ⊗ X) ⊕ (X ⊗ Y) ⊕ (X ⊗ Y) ⊕ (Y ⊗ Y)
              in solve lhs rhs (x ∷ y ∷ a ∷ b ∷ []) refl

  _ : (x y a b : ⟨ R ⟩) → x · a ≡ a · x
  _ = λ x y a b →
              let
                lhs = X ⊗ A
                rhs = A ⊗ X
              in solve lhs rhs (x ∷ y ∷ a ∷ b ∷ []) refl

{-
  this one should work, but doesn't:

  _ : (x y a b : ⟨ R ⟩) → x · (a + b) ≡ a · x + b · x
  _ = λ x y a b →
              let
                lhs = X ⊗ (A ⊕ B)
                rhs = (A ⊗ X) ⊕ (B ⊗ X)
              in solve lhs rhs (x ∷ y ∷ a ∷ b ∷ []) refl

  the reason ist, that lhs and rhs evaluate to definitionally different things:

(0r · x +
 (0r · y +
  ((0r · a + (0r · b + 1r · 1r)) · a +
   ((0r · b + 1r · 1r) · b + 1r · 0r))))
· x
+ 0r

(0r · x +
 (0r · y +
  ((0r · a + (0r · b + 1r · 1r)) · a +
   ((0r · b + 1r · 1r) · b + (0r + 0r · 1r)))))
· x
+ 0r
-}
{-
  '-' is problematic...

  _ : (x y a b : ⟨ R ⟩) → (x + y) · (x - y) ≡ (x · x - (y · y))
  _ = λ x y a b → let
                lhs = (X ⊕ Y) ⊗ (X ⊕ (⊝ Y))
                rhs = (X ⊗ X) ⊕ (⊝ (Y ⊗ Y))
              in solve lhs rhs (x ∷ y ∷ a ∷ b ∷ []) {!!}
-}
