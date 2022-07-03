{-# OPTIONS --safe #-}
module Cubical.Tactics.MonoidSolver.Examples where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.CommMonoid.Base
open import Cubical.Tactics.MonoidSolver.Reflection

private
  variable
    ℓ : Level

module ExamplesMonoid (M : Monoid ℓ) where
  open MonoidStr (snd M)

  _ : ε ≡ ε
  _ = solveMonoid M

  _ : ε · ε · ε ≡ ε
  _ = solveMonoid M

  _ : ∀ x → ε · x  ≡ x
  _ = solveMonoid M

  _ : ∀ x y z → (x · y) · z ≡ x · (y · z)
  _ = solveMonoid M

  _ : ∀ x y z → z · (x · y) · ε · z ≡ z · x · (y · z)
  _ = solveMonoid M

module ExamplesCommMonoid (M : CommMonoid ℓ) where
  open CommMonoidStr (snd M)

  _ : ε ≡ ε
  _ = solveCommMonoid M

  _ : ε · ε · ε ≡ ε
  _ = solveCommMonoid M

  _ : ∀ x → ε · x  ≡ x
  _ = solveCommMonoid M

  _ : ∀ x y z → (x · z) · y ≡ x · (y · z)
  _ = solveCommMonoid M

  _ : ∀ x y  → (x · y) · y · x · (x · y) ≡ x · x · x · (y · y · y)
  _ = solveCommMonoid M
