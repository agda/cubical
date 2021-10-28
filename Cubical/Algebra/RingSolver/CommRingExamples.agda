{-# OPTIONS --safe #-}
module Cubical.Algebra.RingSolver.CommRingExamples where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int.Base hiding (_+_ ; _·_ ; -_ ; _-_)
open import Cubical.Data.Vec.Base

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.NatAsAlmostRing
open import Cubical.Algebra.RingSolver.AlgebraExpression
open import Cubical.Algebra.RingSolver.RawAlgebra renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Algebra.RingSolver.CommRingSolver

private
  variable
    ℓ : Level

module MultivariateSolving (R : CommRing ℓ) where
  -- In scope for debuggin:

  -- In scope for solver use:
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
                lhs = X ·' Y ·' Z
                rhs = Z ·' Y ·' X
              in solve R lhs rhs (x ∷ y ∷ z ∷ []) refl

  _ : (x y z : (fst R)) → x · (y + z) ≡ z · x + y · x
  _ = λ x y z →
              let
                lhs = X ·' (Y +' Z)
                rhs = Z ·' X +' Y ·' X
              in solve R lhs rhs (x ∷ y ∷ z ∷ []) refl


  _ : (x y z : (fst R)) → x · (y - z) ≡ (- z) · x + y · x
  _ = λ x y z →
              let
                lhs = X ·' (Y +' (-' Z))
                rhs = (-' Z) ·' X +' (Y ·' X)
              in solve R lhs rhs (x ∷ y ∷ z ∷ []) refl


  {-
    A bigger example, copied from 'Example.agda'
  -}
  _ : (x y z : (fst R)) → (x + y) · (x + y) · (x + y) · (x + y)
                ≡ x · x · x · x + (scalar R 4) · x · x · x · y + (scalar R 6) · x · x · y · y
                  +  (scalar R 4) · x · y · y · y + y · y · y · y
  _ = λ x y z → let
              lhs = (X +' Y) ·' (X +' Y) ·' (X +' Y) ·' (X +' Y)
              rhs = X ·' X ·' X ·' X
                  +' (K 4) ·' X ·' X ·' X ·' Y
                  +' (K 6) ·' X ·' X ·' Y ·' Y
                  +' (K 4) ·' X ·' Y ·' Y ·' Y
                  +' Y ·' Y ·' Y ·' Y
             in solve R lhs rhs (x ∷ y ∷ z ∷ []) refl


  _ : (x y z : (fst R)) → (x + y) · (x - y) ≡ (x · x - y · y)
  _ = λ x y z →
              let
                lhs = (X +' Y) ·' (X +' (-' Y))
                rhs = (X ·' X) +' (-' (Y ·' Y))
              in solve R lhs rhs (x ∷ y ∷ z ∷ []) refl
