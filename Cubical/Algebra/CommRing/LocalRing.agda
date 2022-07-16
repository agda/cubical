{-
  Definition of local rings.
-}

{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.LocalRing where

-- TODO: imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

-- open import Cubical.Functions.Logic

open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (isProp⊥)

open import Cubical.HITs.PropositionalTruncation as ∥_∥₁

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
-- open import Cubical.Algebra.Ring.Ideal renaming (IdealsIn to IdealsInRing)
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Tactics.CommRingSolver.Reflection

open import Cubical.Relation.Nullary


private
  variable
    ℓ : Level

module _ (R : CommRing ℓ) where
  open Sum (CommRing→Ring R)

  isLocal : Type ℓ
  isLocal =
    {n : _} →
    (xs : FinVec ⟨ R ⟩ n) →
    ∑ xs ∈ R ˣ →
    ∃[ i ∈ Fin n ] (xs i ∈ R ˣ)

  isPropIsLocal : isProp isLocal
  isPropIsLocal = isPropImplicitΠ λ _ → isPropΠ2 λ _ _ → squash₁
