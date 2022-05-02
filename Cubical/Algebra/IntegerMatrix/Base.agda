{-

Matrix with coefficients in integers

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.IntegerMatrix.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (const)
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat
  hiding   (_·_)
  renaming (_+_ to _+ℕ_ ; +-assoc to +Assocℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
  using    (m∣n→m≤n)
  renaming (∣-trans to ∣ℕ-trans)
open import Cubical.Data.Int
  hiding   (_+_ ; _·_ ; _-_ ; -_ ; addEq)
open import Cubical.Data.Int.Divisibility
open import Cubical.Data.FinData

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit  as Unit
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Algebra.Matrix
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
  renaming (ℤ to ℤRing)

open import Cubical.Relation.Nullary
open import Cubical.Induction.WellFounded

private
  variable
    m n k : ℕ

open CommRingStr (ℤRing .snd)
open Coefficient  ℤRing
open Sum         (CommRing→Ring ℤRing)

-- Using well-foundedness to do induction

Norm : ℤ → Type
Norm n = Acc _<_ (abs n)


-- Divisibility of matrix elements

∣-sum :
    (a : ℤ)(V : FinVec ℤ n)
  → ((i : Fin n) → a ∣ V i)
  → a ∣ ∑ V
∣-sum {n = 0} _ _ _ = ∣-zeroʳ
∣-sum {n = suc n} _ _ p = ∣-+ (p zero) (∣-sum _ _ (p ∘ suc))

∣-left⋆ :
    (a : ℤ)(M : Mat m n)(N : Mat n k)
  → ((i : Fin m)(j : Fin n) → a ∣ M i j)
  →  (i : Fin m)(j : Fin k) → a ∣ (M ⋆ N) i j
∣-left⋆ a M N div i j =
  ∣-sum a (λ l → M i l · N l j) (λ l → ∣-left· (div i l))

∣-right⋆ :
    (a : ℤ)(M : Mat m n)(N : Mat n k)
  → ((i : Fin n)(j : Fin k) → a ∣ N i j)
  →  (i : Fin m)(j : Fin k) → a ∣ (M ⋆ N) i j
∣-right⋆ a M N div i j =
  ∣-sum a (λ l → M i l · N l j) (λ l → ∣-right· {n = M i l} (div l j))

open SimRel
open Sim

sim∣ :
    (a : ℤ)(M : Mat m n)
  → (sim : Sim M)
  → ((i : Fin m)(j : Fin n) → a ∣ M i j)
  →  (i : Fin m)(j : Fin n) → a ∣ sim .result i j
sim∣ a M sim div i j =
  subst (a ∣_) (λ t → sim .simrel .transEq (~ t) i j)
    (∣-left⋆ _ _ (sim .simrel .transMatR)
    (∣-right⋆ _ (sim .simrel .transMatL) _ div) i j)


-- Find a pivot to begin reduction

data PivotOrNot (a : ℤ)(M : Mat (suc m) (suc n)) : Type where
  pivot   : (i : Fin (suc m))(j : Fin (suc n))(p : ¬ a ∣ M i j) → PivotOrNot a M
  noPivot : ((i : Fin (suc m))(j : Fin (suc n)) → a ∣ M i j) → PivotOrNot a M

findPivot : (a : ℤ)(M : Mat (suc m) (suc n)) → PivotOrNot a M
findPivot a M =
  let  pivot? = ∀Dec2 (λ i j → a ∣ M i j) (λ _ _ → dec∣ _ _) in
  case pivot?
  return (λ _ → PivotOrNot a M) of λ
  { (inl p) → noPivot p
  ; (inr p) → pivot  (p .fst) (p .snd .fst) (p . snd .snd) }

-- Find an non-zero element

data NonZeroOrNot (M : Mat (suc m) (suc n)) : Type where
  hereIs  : (i : Fin (suc m))(j : Fin (suc n))(p : ¬ M i j ≡ 0) → NonZeroOrNot M
  allZero : M ≡ 𝟘 → NonZeroOrNot M

findNonZero : (M : Mat (suc m) (suc n)) → NonZeroOrNot M
findNonZero M =
  let  nonZero? = ∀Dec2 (λ i j → M i j ≡ 0) (λ _ _ → discreteℤ _ 0) in
  case nonZero?
  return (λ _ → NonZeroOrNot M) of λ
  { (inl p) → allZero (λ t i j → p i j t)
  ; (inr p) → hereIs  (p .fst) (p .snd .fst) (p . snd .snd) }
