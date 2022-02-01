{-

Matrix with coefficients in integers

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Matrix.IntegerCoefficient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (const)
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat hiding (_·_) renaming (_+_ to _+ℕ_ ; +-assoc to +Assocℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
  using    (m∣n→m≤n)
  renaming (∣-trans to ∣ℕ-trans)
open import Cubical.Data.Int hiding (_+_ ; _·_ ; _-_ ; -_ ; addEq)
open import Cubical.Data.Int.Divisibility
open import Cubical.Data.FinData

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit  as Unit
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Matrix
open import Cubical.Algebra.Matrix.RowTransformation
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.Matrix.Elementaries

open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤ to ℤRing)

open import Cubical.Induction.WellFounded

private
  variable
    m n k : ℕ

open CommRingStr      (ℤRing .snd)
open Sum              (CommRing→Ring ℤRing)

open Coefficient ℤRing
open LinearTransformation ℤRing
open Bézout

open SimRel
open Sim

-- The elementary transformations needed

open ElemTransformation ℤRing
open ElemTransformationℤ

open SwapFirstRow
open SwapPivot

open AddFirstRow

open RowsImproved
open ColsImproved

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

sim∣ :
    (a : ℤ)(M : Mat m n)
  → (sim : Sim M)
  → ((i : Fin m)(j : Fin n) → a ∣ M i j)
  →  (i : Fin m)(j : Fin n) → a ∣ sim .result i j
sim∣ a M sim div i j =
  subst (a ∣_) (λ t → sim .simrel .transEq (~ t) i j)
    (∣-left⋆ _ _ (sim .simrel .transMatR)
    (∣-right⋆ _ (sim .simrel .transMatL) _ div) i j)

-- Operations used in the reduction step

record RowsImprovedTrick (M : Mat (suc m) (suc n)) : Type where
  field
    sim : Sim M

    div     : (i : Fin (suc m)) → sim .result zero zero ∣ M i zero
    const   : (i : Fin m) → sim .result (suc i) zero ≡ sim .result zero zero
    nonZero : ¬ sim .result zero zero ≡ 0

open RowsImprovedTrick

improveRowsTrick : (M : Mat (suc m) (suc n))(p : ¬ M zero zero ≡ 0) → RowsImprovedTrick M
improveRowsTrick M p =
  let improveM = improveRows M p
      trickM = addFirstRow (improveM .sim .result)
      inv₀₀ = (λ t → trickM .inv₀ t zero)
  in  record
        { sim = compSim (improveM .sim) (trickM .sim)
        ; div     = (λ i → subst (λ a → a ∣ M i zero) inv₀₀ (improveM .div i))
        ; const   =
              (λ i → sym (trickM .addEq i zero)
            ∙ (λ t → improveM .sim .result zero zero + improveM .vanish i t)
            ∙ +Rid _ ∙ inv₀₀)
        ; nonZero = (λ r → improveM .nonZero (inv₀₀ ∙ r)) }


-- Find a pivot to begin reduction

data PivotOrNot (a : ℤ)(M : Mat (suc m) (suc n)) : Type where
  pivot   : (i : Fin (suc m))(j : Fin (suc n))(p : ¬ a ∣ M i j) → PivotOrNot a M
  noPivot : ((i : Fin (suc m))(j : Fin (suc n)) → a ∣ M i j) → PivotOrNot a M

findPivot : (a : ℤ)(M : Mat (suc m) (suc n)) → PivotOrNot a M
findPivot a M =
  let  pivot? = ∀Dec2 (λ i j → a ∣ M i j) (λ _ _ → dec∣ _ _) in
  case pivot?
  return (λ _ → PivotOrNot a M) of
    λ { (inl p) → noPivot p
      ; (inr p) → pivot  (p .fst) (p .snd .fst) (p . snd .snd) }

-- Reduce the pivot

record PivotReduced (M : Mat (suc m) (suc n)) : Type where
  field
    sim : Sim M

    nonZero : ¬ sim .result zero zero ≡ 0
    div : (i : Fin (suc m))(j : Fin (suc n)) → sim .result zero zero ∣ sim .result i j

open PivotReduced

simPivotReduced : {M : Mat (suc m) (suc n)}
  (SimM : Sim M)(prSimM : PivotReduced (SimM .result)) → PivotReduced M
simPivotReduced simM prSimM .sim = compSim simM (prSimM .sim)
simPivotReduced _ prSimM .nonZero = prSimM .nonZero
simPivotReduced _ prSimM .div     = prSimM .div

-- Helpers to do structural recursion
record RowsImprovedTrickHelper (M : Mat (suc m) (suc n)) : Type where
  field
    sim : Sim M

    const   : (i : Fin m) → sim .result (suc i) zero ≡ sim .result zero zero
    nonZero : ¬ sim .result zero zero ≡ 0

open RowsImprovedTrickHelper

record InductionHelper (M : Mat (suc m) (suc n)) : Type where
  field
    improved : RowsImprovedTrickHelper M
    normIneq : abs (improved .sim .result zero zero) < abs (M zero zero)

open InductionHelper

reducePivot-induction-helper :
    (M : Mat (suc m) (suc n))
  → (p : ¬ M zero zero ≡ 0)
  → (j : Fin n)(q : ¬ M zero zero ∣ M zero (suc j))
  → InductionHelper M
reducePivot-induction-helper M p j q =
  let improveColsM = improveCols M p
      improveM = improveRowsTrick (improveColsM .sim .result) (improveColsM .nonZero)
  in  record
      { improved =
          record
            { sim = compSim (improveColsM .sim) (improveM .sim)
            ; const   = improveM .const
            ; nonZero = improveM .nonZero }
      ; normIneq =
          ≤<-trans
            (m∣n→m≤n (¬x≡0→¬abs≡0 (improveColsM .nonZero)) (∣→∣ℕ (improveM .div zero)))
            (stDivIneq p q (improveColsM .div zero) (improveColsM .div (suc j))) }

reducePivot-helper :
    (M : Mat (suc m) (suc n))
  → (p : ¬ M zero zero ≡ 0)(h : Norm (M zero zero))
  → (cst : (i : Fin m) → M (suc i) zero ≡ M zero zero)
  → (pivot? : PivotOrNot (M zero zero) M)
  → PivotReduced M
reducePivot-helper M _ _ _ (noPivot q) .sim     = idSim M
reducePivot-helper _ p _ _ (noPivot q) .nonZero = p
reducePivot-helper _ _ _ _ (noPivot q) .div     = q
reducePivot-helper _ _ _ _ (pivot zero zero q) =
  Empty.rec (q (∣-refl refl))
reducePivot-helper M _ _ cst (pivot (suc i) zero q) =
  Empty.rec (q (subst (λ a → (M zero zero) ∣ a) (sym (cst i)) (∣-refl refl)))
reducePivot-helper M p (acc ind) _ (pivot zero (suc j) q) =
  let helperM = reducePivot-induction-helper M p j q
      reduceM =
        reducePivot-helper
          (helperM .improved .sim .result)
          (helperM .improved .nonZero)
          (ind _ (helperM .normIneq))
          (helperM .improved .const) (findPivot _ _)
  in  simPivotReduced (helperM .improved .sim) reduceM
reducePivot-helper M p (acc ind) cst (pivot (suc i) (suc j) q) =
  let swapM = swapFirstRow i M
      --swapNorm    = subst (λ a → abs a < (suc N)) (sym (cst i) ∙ (swapM .swapEq zero)) h
      swapNonZero = (λ r → p (sym (cst i) ∙ (swapM .swapEq zero) ∙ r))
      swapDiv =
        (transport ((λ t → ¬ cst i (~ t) ∣ M (suc i) (suc j))
                  ∙ (λ t → ¬ swapM .swapEq zero t ∣ swapM .swapEq (suc j) t)) q)
      helperM  = reducePivot-induction-helper _ swapNonZero j swapDiv
      swapNorm =
        subst (λ a → abs (helperM . improved .sim .result zero zero) < abs a)
              (sym (sym (cst i) ∙ (swapM .swapEq zero))) (helperM .normIneq)
      reduceM  =
        reducePivot-helper
          (helperM .improved .sim .result)
          (helperM .improved .nonZero)
          (ind _ swapNorm)
          --(<≤-trans (helperM .normIneq) (pred-≤-pred swapNorm))
          (helperM .improved .const) (findPivot _ _)
  in  simPivotReduced (compSim (swapM .sim) (helperM .improved .sim)) reduceM

-- The reduction step

reducePivot : (M : Mat (suc m) (suc n))(p : ¬ M zero zero ≡ 0) → PivotReduced M
reducePivot M p =
  let improveM = improveRowsTrick M p
      reduceM  =
        reducePivot-helper
          (improveM .sim .result)
          (improveM .nonZero)
          (<-wellfounded _)
          (improveM .const) (findPivot _ _)
  in  simPivotReduced (improveM .sim) reduceM

-- Find an non-zero element

data NonZeroOrNot (M : Mat (suc m) (suc n)) : Type where
  hereIs  : (i : Fin (suc m))(j : Fin (suc n))(p : ¬ M i j ≡ 0) → NonZeroOrNot M
  allZero : M ≡ 𝟘 → NonZeroOrNot M

findNonZero : (M : Mat (suc m) (suc n)) → NonZeroOrNot M
findNonZero M =
  let  nonZero? = ∀Dec2 (λ i j → M i j ≡ 0) (λ _ _ → discreteℤ _ 0) in
  case nonZero?
  return (λ _ → NonZeroOrNot M) of
    λ { (inl p) → allZero (λ t i j → p i j t)
      ; (inr p) → hereIs  (p .fst) (p .snd .fst) (p . snd .snd) }

-- One induction step towards Smith normal form

record SmithStep (M : Mat (suc m) (suc n)) : Type where
  field
    sim : Sim M

    firstColClean : (i : Fin m) → sim .result (suc i) zero ≡ 0
    firstRowClean : (j : Fin n) → sim .result zero (suc j) ≡ 0

    nonZero : ¬ sim .result zero zero ≡ 0
    div : (i : Fin m)(j : Fin n) → sim .result zero zero ∣ sim .result (suc i) (suc j)

open SmithStep

smithStep-helper : (M : Mat (suc m) (suc n)) → NonZeroOrNot M → SmithStep M ⊎ (M ≡ 𝟘)
smithStep-helper _ (allZero p) = inr p
smithStep-helper M (hereIs i j p) =
  let swapM = swapPivot i j M
      swapNonZero = (λ r → p (swapM .swapEq ∙ r))
      reduceM = reducePivot (swapM .sim .result) swapNonZero
      improveColM = improveCols (reduceM .sim .result) (reduceM .nonZero)
      divCol = (λ i j → bézoutRows-commonDivInv _ (reduceM .nonZero) (λ i j → reduceM .div j i) j i)
      improveRowM = improveRows (improveColM .sim .result) (improveColM .nonZero)
      invCol = bézoutRows-inv _ (improveColM .nonZero) (λ i → divCol (suc i) zero)
  in  inl record
        { sim = compSim (swapM .sim) (compSim (reduceM .sim) (compSim (improveColM .sim) (improveRowM .sim)))
        ; firstColClean = improveRowM .vanish
        ; firstRowClean = (λ j → (λ t → invCol (~ t) (suc j)) ∙ improveColM .vanish j)
        ; nonZero = improveRowM .nonZero
        ; div     = (λ i j → bézoutRows-commonDivInv _ (improveColM .nonZero) divCol (suc i) (suc j)) }

smithStep : (M : Mat (suc m) (suc n)) → SmithStep M ⊎ (M ≡ 𝟘)
smithStep M = smithStep-helper M (findNonZero _)
