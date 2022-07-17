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
open import Cubical.Foundations.Univalence using (hPropExt)

-- open import Cubical.Functions.Logic

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty using (isProp⊥)

open import Cubical.HITs.PropositionalTruncation as ∥_∥₁

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.Ring
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
    open CommRingStr (snd R)
    open Units R

    1≢0 : ¬ (1r ≡ 0r)
    1≢0 1≡0 = ∥_∥₁.rec isProp⊥ (¬Fin0 ∘ fst) (local xs 0∈Rˣ)
      where
      xs : FinVec ⟨ R ⟩ 0
      xs ()
      0∈Rˣ : 0r ∈ R ˣ
      0∈Rˣ = subst (_∈ (R ˣ)) 1≡0 RˣContainsOne

    invertibleInBinarySum :
      {x y : ⟨ R ⟩} →
      x + y ∈ R ˣ →
      ∥ (x ∈ R ˣ) ⊎  (y ∈ R ˣ) ∥₁
    invertibleInBinarySum {x = x} {y = y} x+yInv =
      ∥_∥₁.map Σ→⊎ (local {n = 2} xy (subst (_∈ R ˣ) (∑xy≡x+y x y) x+yInv))
      where
      xy : FinVec ⟨ R ⟩ 2
      xy zero = x
      xy one = y
      ∑xy≡x+y : (x y : ⟨ R ⟩) → x + y ≡ x + (y + 0r)
      ∑xy≡x+y = solve R
      Σ→⊎ : Σ[ i ∈ Fin 2 ] xy i ∈ R ˣ → (x ∈ R ˣ) ⊎ (y ∈ R ˣ)
      Σ→⊎ (zero , xInv) = inl xInv
      Σ→⊎ (one , yInv) = inr yInv

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

    private
      nonInvertibles : ℙ ⟨ R ⟩
      nonInvertibles = λ x → (¬ (x ∈ R ˣ)) , isProp→ isProp⊥

    open CommIdeal.isCommIdeal

    nonInvertiblesFormIdeal : CommIdeal.isCommIdeal R nonInvertibles
    +Closed nonInvertiblesFormIdeal {x = x} {y = y} xNonInv yNonInv x+yInv =
      ∥_∥₁.rec isProp⊥ (⊎.rec xNonInv yNonInv) (invertibleInBinarySum x+yInv)
    contains0 nonInvertiblesFormIdeal (x , 0x≡1) =
      1≢0 (sym 0x≡1 ∙ useSolver _)
      where
        useSolver : (x : ⟨ R ⟩) → 0r · x ≡ 0r
        useSolver = solve R
    ·Closed nonInvertiblesFormIdeal {x = x} r xNonInv rxInv =
      xNonInv (snd (RˣMultDistributing r x rxInv))


  module Characterizations where

    module OneMinus where
      open CommRingStr (snd R)

      Alternative : Type ℓ
      Alternative = (¬ 1r ≡ 0r) × ((x : ⟨ R ⟩) → ∥ (x ∈ R ˣ) ⊎ (1r - x ∈ R ˣ) ∥₁ )

      isPropAlternative : isProp Alternative
      isPropAlternative =
        isProp×
          (isProp→ isProp⊥)
          (isPropΠ (λ _ → isPropPropTrunc))

      private
        isLocal→Alternative : isLocal → Alternative
        isLocal→Alternative local =
            1≢0
          , λ x → invertibleInBinarySum (subst (_∈ R ˣ) (1≡x+1-x x) RˣContainsOne)
          where
          1≡x+1-x : (x : ⟨ R ⟩) → 1r ≡ x + (1r - x)
          1≡x+1-x = solve R
          open Consequences local
          open Units R

        alternative→isLocal : Alternative → isLocal
        alternative→isLocal = {!!}

      path : isLocal ≡ Alternative
      path =
        hPropExt
          isPropIsLocal
          isPropAlternative
          isLocal→Alternative
          alternative→isLocal
