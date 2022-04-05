{-

The Existence of Smith Normal Form for Integer Matrices (KANG Rongji, Jan. 2022)

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.IntegerMatrix.Smith.Normalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

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
open import Cubical.Data.Sum

open import Cubical.Algebra.Matrix
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.Matrix.Elementaries
open import Cubical.Algebra.IntegerMatrix.Base
open import Cubical.Algebra.IntegerMatrix.Elementaries
open import Cubical.Algebra.IntegerMatrix.Smith.NormalForm

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
open Sim

-- The elementary transformations needed

open ElemTransformation ℤRing
open ElemTransformationℤ
open SwapFirstRow
open SwapPivot
open AddFirstRow
open RowsImproved
open ColsImproved


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


private
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
            (helperM .improved .const) (findPivot _ _)
    in  simPivotReduced (compSim (swapM .sim) (helperM .improved .sim)) reduceM

-- The reduction of pivot

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


-- One induction step towards normal form

open isSmithNormal
open Smith

record SmithStep (M : Mat (suc m) (suc n)) : Type where
  field
    sim : Sim M

    firstColClean : (i : Fin m) → sim .result (suc i) zero ≡ 0
    firstRowClean : (j : Fin n) → sim .result zero (suc j) ≡ 0

    nonZero : ¬ sim .result zero zero ≡ 0
    div : (i : Fin m)(j : Fin n) → sim .result zero zero ∣ sim .result (suc i) (suc j)

open SmithStep

private
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


-- The main procedure

private
  smithReduction-helper :
      (M : Mat (suc m) (suc n))(step : SmithStep M)
    → step .sim .result ≡ step .sim .result zero zero ⊕ sucMat (step .sim .result)
  smithReduction-helper M step t zero zero = step .sim .result zero zero
  smithReduction-helper M step t zero (suc j) = step .firstRowClean j t
  smithReduction-helper M step t (suc i) zero = step .firstColClean i t
  smithReduction-helper M step t (suc i) (suc j) = step .sim .result (suc i) (suc j)

consIsSmithNormal :
    (a : ℤ)(M : Mat m n)
  → (p : ¬ a ≡ 0)
  → (div : (i : Fin m)(j : Fin n) → a ∣ M i j)
  → isSmithNormal M → isSmithNormal (a ⊕ M)
consIsSmithNormal a _ p d isNorm .divs = cons a (isNorm .divs) (smith∣ a isNorm p d)
consIsSmithNormal _ _ _ _ isNorm .rowNull = isNorm .rowNull
consIsSmithNormal _ _ _ _ isNorm .colNull = isNorm .colNull
consIsSmithNormal _ _ _ _ isNorm .rowEq = (λ t → suc (isNorm .rowEq t))
consIsSmithNormal _ _ _ _ isNorm .colEq = (λ t → suc (isNorm .colEq t))
consIsSmithNormal a _ _ _ isNorm .matEq = (λ t → a ⊕ isNorm .matEq t)

smithReduction :
    (a : ℤ)(M : Mat m n)
  → (p : ¬ a ≡ 0)
  → (div : (i : Fin m)(j : Fin n) → a ∣ M i j)
  → Smith M → Smith (a ⊕ M)
smithReduction a _ _ _ smithnorm .sim = ⊕Sim a (smithnorm .sim)
smithReduction a _ p d smithnorm .isnormal =
  consIsSmithNormal a _ p (sim∣ _ _ (smithnorm .sim) d) (smithnorm .isnormal)


-- The Existence of Smith Normal Form

smith : (M : Mat m n) → Smith M
smith {m = 0} = smithEmpty
smith {m = suc m} {n = 0} = smithEmptyᵗ
smith {m = suc m} {n = suc n} M = helper (smithStep _)
  where
  helper : SmithStep M ⊎ (M ≡ 𝟘) → Smith M
  helper (inr p) = subst Smith (sym p) smith𝟘
  helper (inl stepM) =
    let sucM = sucMat (stepM .sim .result)
        smithM = smithReduction _ _ (stepM .nonZero) (stepM .div) (smith sucM)
    in  simSmith (compSim (stepM .sim) (≡Sim (smithReduction-helper _ stepM))) smithM

-- TODO: The uniqueness of Smith normal form up to unit multiplication.
