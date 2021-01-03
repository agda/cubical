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

  test :  1r · (1r + 0r)
        ≡ (1r · 0r) + 1r
  test = solve R
