{-# OPTIONS --safe #-}

module Cubical.Algebra.MonoidSolver.Examples where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.MonoidSolver.ReflectionSolving

private
  variable
    ℓ : Level

module test (M : Monoid ℓ) where
  open MonoidStr (snd M)

  _ : ε ≡ ε
  _ = solve M

  _ : ε · ε · ε ≡ ε
  _ = solve M

  _ : ∀ x → ε · x  ≡ x
  _ = solve M

  _ : ∀ x y z → (x · y) · z ≡ x · (y · z)
  _ = solve M

  _ : ∀ x y z → z · (x · y) · ε · z ≡ z · x · (y · z)
  _ = solve M


