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

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (isProp⊥)

open import Cubical.HITs.PropositionalTruncation as ∥_∥₁

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
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
    {n : ℕ} →
    (xs : FinVec ⟨ R ⟩ n) →
    ∑ xs ∈ R ˣ →
    ∃[ i ∈ Fin n ] (xs i ∈ R ˣ)

  isPropIsLocal : isProp isLocal
  isPropIsLocal = isPropImplicitΠ λ _ → isPropΠ2 λ _ _ → isPropPropTrunc

  module Consequences (local : isLocal) where
    open RingStr (snd (CommRing→Ring R))
    open Units R

    1≢0 : ¬ (1r ≡ 0r)
    1≢0 1≡0 = ∥_∥₁.rec isProp⊥ (¬Fin0 ∘ fst) (local xs 0∈Rˣ)
      where
      xs : FinVec ⟨ R ⟩ 0
      xs ()
      0∈Rˣ : 0r ∈ R ˣ
      0∈Rˣ = subst (_∈ (R ˣ)) 1≡0 RˣContainsOne

    onLinearCombinations :
      {n : ℕ} →
      (α xs : FinVec ⟨ R ⟩ n) →
      1r ≡ linearCombination R α xs →
      ∃[ i ∈ Fin n ] xs i ∈ R ˣ
    onLinearCombinations {n = n} α xs 1≡αxs = αxsHasInv→xsHasInv αxsHasInvertible
      where
      αxs : FinVec ⟨ R ⟩ n
      αxs i = α i · xs i
      αxsHasInvertible : ∃[ i ∈ Fin n ] αxs i ∈ R ˣ
      αxsHasInvertible = local αxs (subst (_∈ R ˣ) 1≡αxs RˣContainsOne)
      αxsHasInv→xsHasInv : ∃[ i ∈ Fin n ] αxs i ∈ R ˣ → ∃[ i ∈ Fin n ] xs i ∈ R ˣ
      αxsHasInv→xsHasInv =
        ∥_∥₁.rec
          isPropPropTrunc
          λ{(i , αxsi∈Rˣ) → ∣ i , snd (RˣMultDistributing (α i) (xs i) αxsi∈Rˣ) ∣₁}

    onFGIdeals :
      {n : ℕ} →
      (xs : FinVec ⟨ R ⟩ n) →
      1r ∈ fst (generatedIdeal R xs) →
      ∃[ i ∈ Fin n ] xs i ∈ R ˣ
    onFGIdeals xs =
      ∥_∥₁.rec
        isPropPropTrunc
        λ{(α , 1≡αxs) → onLinearCombinations α xs 1≡αxs}
