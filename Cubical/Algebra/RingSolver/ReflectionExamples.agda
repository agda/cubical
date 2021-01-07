{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.ReflectionExamples where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.ReflectionSolving

private
  variable
    ℓ : Level

module Test (R : CommRing {ℓ}) where
  open CommRingStr (snd R)
  open CommRingMinusOperator R

  _ :   1r · (1r + 0r)
      ≡ (1r · 0r) + 1r
  _ = solve R

  _ :   1r · 0r + (1r - 1r)
      ≡ 0r - 0r
  _ = solve R

  _ : (x : fst R) → x ≡ x
  _ = solve R

  _ : (x y : fst R) → x ≡ x
  _ = solve R

