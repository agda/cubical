{-
  Define finitely generated ideals of commutative rings and
  show that they are an ideal.
  Parts of this should be reusable for explicit constructions
  of free modules over a finite set.
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.FGIdeal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.FinData hiding (elim)
open import Cubical.Data.Nat using (ℕ)

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.Ring.QuotientRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.RingSolver.ReflectionSolving

private
  variable
    ℓ : Level

module _ (Ring@(R , str) : CommRing ℓ) where
  infixr 5 _holds
  _holds : hProp ℓ → Type ℓ
  P holds = fst P
  open CommRingStr str
  open RingTheory (CommRing→Ring Ring)
  open Sum (CommRing→Ring Ring)

  linearCombination : {n : ℕ} → FinVec R n → FinVec R n → R
  linearCombination α V = ∑ (λ i → α i · V i)

  sumDist+ : ∀ {n : ℕ} (α β V : FinVec R n)
           → linearCombination (λ i → α i + β i) V ≡ linearCombination α V + linearCombination β V
  sumDist+ α β V = ∑Ext (λ i → ·Ldist+ (α i) (β i) (V i)) ∙ ∑Split (λ i → α i · V i) (λ i → β i · V i)

  dist- : ∀ {n : ℕ} (α V : FinVec R n)
        → linearCombination (λ i → - α i) V ≡ - linearCombination α V
  dist- α V = ∑Ext (λ i → -DistL· (α i) (V i)) ∙ ∑Dist- (λ i → α i · V i)

  dist0 : ∀ {n : ℕ} (V : FinVec R n)
        → linearCombination (replicateFinVec n 0r) V ≡ 0r
  dist0 {n = n} V = ∑Ext (λ i → 0LeftAnnihilates (V i)) ∙ ∑0r n

  isLinearCombination : {n : ℕ} → FinVec R n → R → Type ℓ
  isLinearCombination V x = ∃[ α ∈ FinVec R _ ] x ≡ linearCombination α V

  {- If x and y are linear combinations of l, then (x + y) is
     a linear combination. -}
  isLinearCombination+ : {n : ℕ} {x y : R} (V : FinVec R n)
                         → isLinearCombination V x
                         → isLinearCombination V y
                         → isLinearCombination V (x + y)
  isLinearCombination+ V = map2 λ α β → (λ i → α .fst i + β .fst i)
                                       , cong₂ (_+_) (α .snd) (β .snd) ∙ sym (sumDist+ _ _ V)

  {- If x is a linear combinations of l, then -x is
     a linear combination. -}
  isLinearCombination- : {n : ℕ} {x : R} (V : FinVec R n)
                       → isLinearCombination V x → isLinearCombination V (- x)
  isLinearCombination- V = map λ α → (λ i → - α .fst i) , cong (-_) (α .snd) ∙ sym (dist- _ V)

  {- 0r is the trivial linear Combination -}
  isLinearCombination0 : {n : ℕ} (V : FinVec R n)
                       → isLinearCombination V 0r
  isLinearCombination0 V = ∣ _ , sym (dist0 V) ∣

  {- Linear combinations are stable under left multiplication -}
  isLinearCombinationL· : {n : ℕ} (V : FinVec R n) (r : R) {x : R}
                        → isLinearCombination V x → isLinearCombination V (r · x)
  isLinearCombinationL· V r = map λ α → (λ i → r · α .fst i) , cong (r ·_) (α .snd)
                                                            ∙∙ ∑Mulrdist r (λ i → α .fst i · V i)
                                                            ∙∙ ∑Ext λ i → ·Assoc r (α .fst i) (V i)

  generatedIdeal : {n : ℕ} → FinVec R n → IdealsIn Ring
  generatedIdeal V = makeIdeal Ring
                               (λ x → isLinearCombination V x , isPropPropTrunc)
                               (isLinearCombination+ V)
                               (isLinearCombination0 V)
                               λ r → isLinearCombinationL· V r


open isCommIdeal
genIdeal : {n : ℕ} (R : CommRing ℓ) → FinVec (fst R) n → CommIdeal R
fst (genIdeal R V) x = isLinearCombination R V x , isPropPropTrunc
+Closed (snd (genIdeal R V)) = isLinearCombination+ R V
contains0 (snd (genIdeal R V)) = isLinearCombination0 R V
·Closed (snd (genIdeal R V)) r = isLinearCombinationL· R V r

syntax genIdeal R V = ⟨ V ⟩[ R ]


FGIdealIn : (R : CommRing ℓ) → Type (ℓ-suc ℓ)
FGIdealIn R = Σ[ I ∈ CommIdeal R ] ∃[ n ∈ ℕ ] ∃[ V ∈ FinVec (fst R) n ] I ≡ ⟨ V ⟩[ R ]

