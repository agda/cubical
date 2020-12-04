{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.AlgebraExamples where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Vec.Base

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.NatAsAlmostRing
open import Cubical.Algebra.RingSolver.AlgebraExpression
open import Cubical.Algebra.RingSolver.RawAlgebra renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Algebra.RingSolver.AlgebraHornerForms
open import Cubical.Algebra.RingSolver.AlgebraSolver

private
  variable
    ℓ : Level

module MultivariateSolving (R : CommRing {ℓ}) where
  open CommRingStr (snd R)
  AsAlgebra = CommRing→RawℤAlgebra R

  X : ℤExpr R 3
  X = ∣ Fin.zero

  Y : ℤExpr R 3
  Y = ∣ (suc Fin.zero)

  Z : ℤExpr R 3
  Z = ∣ (suc (suc Fin.zero))

  _ : (x y z : (fst R)) → x · y · z ≡ z · y · x
  _ = λ x y z →
              let
                lhs = X ⊗ Y ⊗ Z
                rhs = Z ⊗ Y ⊗ X
              in solve R lhs rhs (x ∷ y ∷ z ∷ []) refl

  _ : (x y z : (fst R)) → x · (y + z) ≡ z · x + y · x
  _ = λ x y z →
              let
                lhs = X ⊗ (Y ⊕ Z)
                rhs = Z ⊗ X ⊕ Y ⊗ X
              in solve R lhs rhs (x ∷ y ∷ z ∷ []) refl

{-
  still bad, see below:

  _ : (x y z : (fst R)) → (x + y) · (x - y) ≡ (x · x - y · y)
  _ = λ x y z →
              let
                lhs = (X ⊕ Y) ⊗ (X ⊕ (⊝ Y))
                rhs = (X ⊗ X) ⊕ (⊝ (Y ⊗ Y))
              in solve R lhs rhs (x ∷ y ∷ z ∷ []) {!!}




((0r · x + (0r · y + (0r · z + 1r))) · x +
 ((0r · y + (0r · z + 0r)) · y + 0r))
· x
+ (((0r · y + (0r · z + - 1r)) · y + 0r) · y + 0r)

((0r · x + (0r · y + (0r · z + 1r))) · x + 0r) · x +
(((0r · y + (0r · z + - 1r)) · y + 0r) · y + 0r)
-}
