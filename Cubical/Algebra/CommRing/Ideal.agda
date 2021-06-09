{-
  This is mostly for convenience, when working with ideals
  (which are defined for general rings) in a commutative ring.
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Ideal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.Ring.Ideal renaming (IdealsIn to IdealsInRing)
open import Cubical.Algebra.RingSolver.ReflectionSolving

private
  variable
    ℓ : Level

IdealsIn : (R : CommRing ℓ) → Type _
IdealsIn R = IdealsInRing (CommRing→Ring R)

module _ (Ring@(R , str) : CommRing ℓ) where
  open CommRingStr str
  makeIdeal : (I : R → hProp ℓ)
              → (+-closed : {x y : R} → x ∈ I → y ∈ I → (x + y) ∈ I)
              → (0r-closed : 0r ∈ I)
              → (·-closedLeft : {x : R} → (r : R) → x ∈ I → r · x ∈ I)
              → IdealsIn (R , str)
  makeIdeal I +-closed 0r-closed ·-closedLeft = I ,
    (record
       { +-closed = +-closed
       ; -closed = λ x∈I → subst (_∈ I) (useSolver _)
                             (·-closedLeft (- 1r) x∈I)
       ; 0r-closed = 0r-closed
       ; ·-closedLeft = ·-closedLeft
       ; ·-closedRight = λ r x∈I →
                       subst (_∈ I)
                             (·-comm r _)
                             (·-closedLeft r x∈I)
       })
       where useSolver : (x : R) → - 1r · x ≡ - x
             useSolver = solve Ring
