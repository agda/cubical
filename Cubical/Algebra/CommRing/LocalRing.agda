{-
  Definition of (commutative) local rings.

  Note that local rings are more intricate constructively than classically.
  See for example

    "A Course in Constructive Algebra" by Mines, Richman & Ruitenberg, p. 96,

  where (non-commutative) local rings are defined by the two characterizations
  given at the end of this file but without the requirement that 1 is different
  from 0. Or see the nLab page:

    https://ncatlab.org/nlab/show/local+ring
-}

{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.LocalRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Powerset using (_∈_; ℙ)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (hPropExt)

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (FinVec; Fin; ¬Fin0; zero; suc; one)
open import Cubical.Data.Sigma using (∃-syntax; _×_)
open import Cubical.Data.Sum as ⊎ using (_⊎_)
open import Cubical.Data.Empty as ⊥ using (isProp⊥)

open import Cubical.Relation.Nullary using (¬_)

open import Cubical.HITs.PropositionalTruncation as ∥_∥₁ using (isPropPropTrunc; ∣_∣₁; ∥_∥₁)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal using (generatedIdeal; linearCombination)
open import Cubical.Algebra.CommRing.Ideal using (module CommIdeal)
open import Cubical.Algebra.Ring.BigOps using (module Sum)

open import Cubical.Tactics.CommRingSolver


private
  variable
    ℓ : Level

module _ (R : CommRing ℓ) where
  open Sum (CommRing→Ring R) using (∑)

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
      ∥_∥₁.map Σ→⊎ (local {n = 2} xy (subst (_∈ R ˣ) ∑xy≡x+y x+yInv))
      where
      xy : FinVec ⟨ R ⟩ 2
      xy zero = x
      xy one = y
      ∑xy≡x+y : x + y ≡ x + (y + 0r)
      ∑xy≡x+y = solve! R
      Σ→⊎ : Σ[ i ∈ Fin 2 ] xy i ∈ R ˣ → (x ∈ R ˣ) ⊎ (y ∈ R ˣ)
      Σ→⊎ (zero , xInv) = ⊎.inl xInv
      Σ→⊎ (one , yInv) = ⊎.inr yInv

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
      1≢0 (sym 0x≡1 ∙ solve! R)
    ·Closed nonInvertiblesFormIdeal {x = x} r xNonInv rxInv =
      xNonInv (snd (RˣMultDistributing r x rxInv))


  -- Equivalent characterizations of local rings.
  module Characterizations where

    -- A characterization in terms of binary sums of ring elements.
    module BinSum where
      open CommRingStr (snd R)

      BinSum : Type ℓ
      BinSum = (x y : ⟨ R ⟩) → (x + y ∈ R ˣ) → ∥ (x ∈ R ˣ) ⊎ (y ∈ R ˣ) ∥₁

      Alternative : Type ℓ
      Alternative = (¬ 1r ≡ 0r) × BinSum

      isPropAlternative : isProp Alternative
      isPropAlternative =
        isProp×
          (isProp→ isProp⊥)
          (isPropΠ3 (λ _ _ _ → isPropPropTrunc))

      isLocal→Alternative : isLocal → Alternative
      isLocal→Alternative local =
          1≢0
        , λ x y → invertibleInBinarySum
        where
        open Consequences local

      module _ ((1≢0 , binSum) : Alternative) where
        alternative→isLocal : isLocal
        alternative→isLocal {n = ℕ.zero} xs (0⁻¹ , 00⁻¹≡1) =
          ⊥.rec (1≢0 (sym 00⁻¹≡1 ∙ 0x≡0 0⁻¹))
          where
          0x≡0 : (x : ⟨ R ⟩) → 0r · x ≡ 0r
          0x≡0 _ = solve! R
        alternative→isLocal {n = ℕ.suc n} xxs x+∑xsInv =
          ∥_∥₁.rec
            isPropPropTrunc
            (⊎.rec
              (λ xInv → ∣ zero , xInv ∣₁)
              (  ∥_∥₁.map (λ{(i , xsiInv) → (suc i) , xsiInv})
               ∘ alternative→isLocal xs))
            (binSum x (∑ xs) x+∑xsInv)
          where
          x : ⟨ R ⟩
          x = xxs zero
          xs : FinVec ⟨ R ⟩ n
          xs = xxs ∘ suc

      path : isLocal ≡ Alternative
      path =
        hPropExt
          isPropIsLocal
          isPropAlternative
          isLocal→Alternative
          alternative→isLocal

    -- A characterization featuring ring elements of the form 1 - x.
    module OneMinus where
      open CommRingStr (snd R)

      OneMinus : Type ℓ
      OneMinus = (x : ⟨ R ⟩) → ∥ (x ∈ R ˣ) ⊎ (1r - x ∈ R ˣ) ∥₁

      Alternative : Type ℓ
      Alternative = (¬ 1r ≡ 0r) × OneMinus

      isPropAlternative : isProp Alternative
      isPropAlternative =
        isProp×
          (isProp→ isProp⊥)
          (isPropΠ (λ _ → isPropPropTrunc))

      private
        binSum→OneMinus : BinSum.BinSum → OneMinus
        binSum→OneMinus binSum x =
          binSum x (1r - x) (subst (_∈ R ˣ) (solve! R) RˣContainsOne)
          where open Units R

        oneMinus→BinSum : OneMinus → BinSum.BinSum
        oneMinus→BinSum oneMinus x y (s⁻¹ , ss⁻¹≡1) =
          ∥_∥₁.map
            (⊎.map
              (fst ∘ RˣMultDistributing x s⁻¹)
              (fst ∘ RˣMultDistributing y s⁻¹ ∘ subst (_∈ R ˣ) 1-xs⁻¹≡ys⁻¹))
            (oneMinus (x · s⁻¹))
          where
          1-xs⁻¹≡ys⁻¹ : 1r - x · s⁻¹ ≡ y · s⁻¹
          1-xs⁻¹≡ys⁻¹ =
            (1r - x · s⁻¹)             ≡⟨ cong (_- _) (sym ss⁻¹≡1) ⟩
            ((x + y) · s⁻¹ - x · s⁻¹)  ≡⟨ solve! R ⟩
            (y · s⁻¹)                  ∎
          open Units R

        pathFromBinSum : BinSum.Alternative ≡ Alternative
        pathFromBinSum =
          hPropExt
            BinSum.isPropAlternative
            isPropAlternative
            (λ{ (1≢0 , binSum) → 1≢0 , binSum→OneMinus binSum})
            (λ{ (1≢0 , oneMinus) → 1≢0 , oneMinus→BinSum oneMinus})

      path : isLocal ≡ Alternative
      path = BinSum.path ∙ pathFromBinSum
