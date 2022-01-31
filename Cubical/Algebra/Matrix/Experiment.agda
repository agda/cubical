{-# OPTIONS --safe -vprofile.interactive:10 #-}
module Cubical.Algebra.Matrix.Experiment where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (const)
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat hiding (_+_ ; _·_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
  using    (m∣n→m≤n)
  renaming (∣-trans to ∣ℕ-trans)
open import Cubical.Data.Int hiding (_+_ ; _·_ ; _-_ ; -_ ; addEq)
open import Cubical.Data.Int.Divisibility
open import Cubical.Data.FinData

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Matrix
open import Cubical.Algebra.Matrix.RowTransformation
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.Matrix.Elementaries
open import Cubical.Algebra.Matrix.IntegerCoefficient
open import Cubical.Algebra.Matrix.Smith
open import Cubical.Algebra.Matrix.Diagonalization

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
  renaming (ℤ to Ringℤ)
open import Cubical.Algebra.RingSolver.Reflection

private
  variable
    ℓ : Level
    m n k : ℕ

open CommRingStr      (Ringℤ .snd)
open CommRingTheory    Ringℤ
open RingTheory       (CommRing→Ring Ringℤ)
open KroneckerDelta   (CommRing→Ring Ringℤ)
open Sum              (CommRing→Ring Ringℤ)

open Coefficient Ringℤ
open LinearTransformation Ringℤ
open Bézout

open SimRel
open Sim

open ElemTransformation Ringℤ
open ElemTransformationℤ

open SwapFirstRow
open SwapPivot

open RowsImproved
open ColsImproved

open SmithStep

open DiagStep

open RowsImproved

-- Examples

toMat2 : ℤ → ℤ → ℤ → ℤ → Mat 2 2
toMat2 a _ _ _ zero zero = a
toMat2 _ b _ _ zero one  = b
toMat2 _ _ c _ one  zero = c
toMat2 _ _ _ d one  one  = d

toNum2 : Mat 2 2 → ℤ × ℤ × ℤ × ℤ
toNum2 M = M zero zero , M zero one
         , M one  zero , M one  one

AA = toMat2 123 1234 12 32

pattern two = suc one

toMat3 : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → Mat 3 3
toMat3 a _ _ _ _ _ _ _ _ zero zero = a
toMat3 _ b _ _ _ _ _ _ _ zero one  = b
toMat3 _ _ c _ _ _ _ _ _ zero two  = c
toMat3 _ _ _ d _ _ _ _ _ one  zero = d
toMat3 _ _ _ _ e _ _ _ _ one  one  = e
toMat3 _ _ _ _ _ f _ _ _ one  two  = f
toMat3 _ _ _ _ _ _ g _ _ two  zero = g
toMat3 _ _ _ _ _ _ _ h _ two  one  = h
toMat3 _ _ _ _ _ _ _ _ i two  two  = i

toNum3 : Mat 3 3 → ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ
toNum3 M = M zero zero , M zero one  , M zero two
         , M one  zero , M one  one  , M one  two
         , M two  zero , M two  one  , M two  two

BB = toMat3 2 4 4 -6 6 12 10 4 16

p : ¬ pos 2 ≡ 0
p r = Cubical.Data.Nat.snotz (injPos r)

getMat : {M : Mat (suc m) (suc n)} → SmithStep M ⊎ (M ≡ 𝟘) → Mat (suc m) (suc n)
getMat (inl ss) = ss .sim .result
getMat (inr  _) = 𝟘

getMatD : {M : Mat (suc m) (suc n)} → DiagStep M ⊎ (M ≡ 𝟘) → Mat (suc m) (suc n)
getMatD (inl ss) = ss .sim .result
getMatD (inr  _) = 𝟘


open PivotReduced

smithStep-onlyMat-helper : (M : Mat (suc m) (suc n)) → NonZeroOrNot M → Mat (suc m) (suc n)
smithStep-onlyMat-helper _ (allZero _) = 𝟘
smithStep-onlyMat-helper M (hereIs i j p) =
  let swapM = swapPivot i j M
      swapNonZero = (λ r → p (swapM .swapEq ∙ r))
      reduceM = reducePivot (swapM .sim .result) swapNonZero
      improveColM = improveCols (reduceM .sim .result) (reduceM .nonZero)
      improveRowM = improveRows (improveColM .sim .result) (improveColM .nonZero)
  in  improveRowM .sim .result

smithStep-onlyMat : (M : Mat (suc m) (suc n)) → Mat (suc m) (suc n)
smithStep-onlyMat M = smithStep-onlyMat-helper M (findNonZero _)

open PivotReduced

-- Time: 180ms
R1 = toNum2 ((reducePivot (toMat2 2 7 1 6) p) .sim .result)

-- Time: 1,645ms
R1d = toNum2 (getMatD (diagStep (toMat2 2 7 1 6)))

-- Time: 1,997ms
R2 = toNum2 (getMat (smithStep (toMat2 2 7 1 6)))

-- Time: 99,820ms
R3 = toNum2 (getMat (smithStep (toMat2 2 7 4 6)))

-- Time: 6,292ms
R3d = toNum2 (getMatD (diagStep (toMat2 2 7 4 6)))

-- Time: 79,652ms
R4 = toNum2 (getMat (smithStep (toMat2 2 3 4 1)))

-- Time: 2,538ms
R4d = toNum2 (getMatD (diagStep (toMat2 2 3 4 1)))

-- Time: 13,930ms
R5 = toNum2 (getMat (smithStep (toMat2 7 0 -13 0)))

-- Time: 11,267ms
R5d = toNum2 (getMatD (diagStep (toMat2 7 0 -13 0)))

-- Time: 18,386ms
R5d' = toNum2 (getMatD (diagStep (toMat2 7 -13 0 0)))

-- Time: 11,878ms
R6d = toNum2 (getMatD (diagStep (toMat2 7 2 -13 3)))

-- Time: 18ms
rr = bézout 7 -13 .gcd

-- Time: 333ms
rr' = toNum2 (improveRows (toMat2 7 0 -13 0) _ .sim .result)

-- Time: 168,314ms
R6 = toNum2 (getMat (smithStep (toMat2 7 -13 0 0)))

-- Time: 32,509ms
R7 = toNum2 (getMat (smithStep (toMat2 2 1 0 0)))

-- Time: 2,483ms
R7p  = toNum2 (reducePivot (toMat2 2 1 0 0) p .sim .result)

-- Time: 30,656ms
R7o  = toNum2 (smithStep-onlyMat (toMat2 2 1 0 0))

smithStep-noSwapOnlyMat-helper : (M : Mat (suc m) (suc n)) → NonZeroOrNot M → Mat (suc m) (suc n)
smithStep-noSwapOnlyMat-helper _ (allZero _) = 𝟘
smithStep-noSwapOnlyMat-helper M (hereIs (suc i) zero _) = 𝟘
smithStep-noSwapOnlyMat-helper M (hereIs i (suc j) _) = 𝟘
smithStep-noSwapOnlyMat-helper M (hereIs zero zero p) =
  let reduceM = reducePivot M p
      improveColM = improveCols (reduceM .sim .result) _
      --improveRowM = improveRows (improveColM .sim .result) (improveColM .nonZero)
  in  improveColM .sim .result

smithStep-noSwapOnlyMat : (M : Mat (suc m) (suc n)) → Mat (suc m) (suc n)
smithStep-noSwapOnlyMat M = smithStep-noSwapOnlyMat-helper M (findNonZero _)

-- Time: 2,532ms
-- Time: 5,835ms
R7ons  = toNum2 (smithStep-noSwapOnlyMat (toMat2 2 1 0 0))

-- Time: 9ms
R7'pp  = toNum2 (improveRows (toMat2 1 0 1 0) _ .sim .result)

R7x = toNum2 (improveRows (toMat2 2 1 0 0) p .sim .result)

-- Time: 1,738ms
R7' = toNum2 (getMat (smithStep (toMat2 2 0 1 0)))

-- Time: 1,639ms
R7oo = toNum2 (smithStep-onlyMat (toMat2 2 0 1 0))

-- Time: 158ms
R7'p = toNum2 (reducePivot (toMat2 2 0 1 0) p .sim .result)

-- Time: 206ms
R8 = toNum2 (reducePivot (toMat2 2 7 3 6) p .sim .result)

-- Time: 6,054ms
R9 = toNum2 (reducePivot (toMat2 2 3 4 1) p .sim .result)

-- Time: 2,011ms
R10 = toNum3 (getMatD (diagStep BB))

open isSmithNormal
open Smith
open isDiagonal
open Diag

-- Time: 951ms
elem0 = smith (toMat2 2 0 1 0) .isnormal .divs .fst

-- Time: 734ms
elem0d = diagonalize (toMat2 2 0 1 0) .isdiag .divs .fst

-- Time: 3,742ms
elem1 = smith (toMat2 2 7 1 6) .isnormal .divs .fst

-- Time: 1,767ms
elem1d = diagonalize (toMat2 2 7 1 6) .isdiag .divs .fst

-- Time: 3,671ms
elem2 = smith (toMat2 2 7 3 6) .isnormal .divs .fst

-- Time: 1,780ms
elem2d = diagonalize (toMat2 2 7 3 6) .isdiag .divs .fst

-- Time: 147,617ms
elem3 = smith (toMat2 2 3 4 1) .isnormal .divs .fst

-- Time: Time: 2,729ms
elem3d = diagonalize (toMat2 2 3 4 1) .isdiag .divs .fst

-- Time: 16,297ms
elem4 = smith (toMat2 2 1 0 0) .isnormal .divs .fst

-- Time: 981ms
elem4d = diagonalize (toMat2 2 1 0 0) .isdiag .divs .fst

BB''''' = toMat3 2 4 4 1 6 5 10 4 16

elem5 = smith BB''''' .isnormal .divs .fst

elem5d = diagonalize BB''''' .isdiag .divs .fst

elem5d' = diagonalize BB .isdiag .divs .fst

elem6 = smith (toMat3 1 0 0 0 1 0 0 0 1) .isnormal .divs .fst

--Time: 8,387ms
elem6d = diagonalize (toMat3 1 0 0 0 1 0 0 0 1) .isdiag .divs .fst

--Time: 456,425ms
elemxd = diagonalize (toMat3 2 3 1 2 2 3 1 1 0) .isdiag .divs .fst

-- Time: 678ms
elem7 = smith (toMat2 1 0 0 1) .isnormal .divs .fst

-- Time: 10,190ms
elem8 = smith (toMat3 1 0 0 0 0 0 0 0 0) .isnormal .divs .fst

-- Time: 592ms
elem8d = diagonalize (toMat3 1 0 0 0 0 0 0 0 0) .isdiag .divs .fst

elem9 = smith (toMat3 1 0 0 0 0 0 0 0 0) .isnormal .divs .fst

-- Time: 1ms
elem10 = smith (toMat3 0 0 0 0 0 0 0 0 0) .isnormal .divs .fst

-- Time: 11,766ms
elem11 = smith (toMat3 0 0 0 0 0 0 0 0 1) .isnormal .divs .fst

CCC   = toNum3 (improveCols BB p .sim .result)

CCCC  = toNum3 (improveCols BB p .sim .simrel .transMatR)

CCCCC = toNum3 (improveCols BB p .sim .simrel .isInvTransR .fst)

M1 = toNum3 (getMat (smithStep BB))

-- Time: 385,077ms
M2 = toNum2 (getMat (smithStep (toMat2 4 7 2 6)))

-- Time: 18ms
bc : ℤ × ℤ
bc = bézout 1 0 .coef₁ , bézout 1 0 .coef₂

bc' : ℤ × ℤ
bc' = bézout 0 1 .coef₁ , bézout 0 1 .coef₂

bc'' : ℤ × ℤ
bc'' = bézout 0 0 .coef₁ , bézout 0 0 .coef₂

open import Cubical.Data.Bool

ax : Bool
ax = case (findPivot 2 BB)
     return (λ _ → Bool) of
      λ { (pivot _ _ _) → true
        ; (noPivot _)   → false }

record NonZeroElem (M : Mat (suc m) (suc n)) : Type where
  constructor nonzeroelem
  field
    coord : Fin (suc m) × Fin (suc n)
    nonZero : ¬ M (coord .fst) (coord .snd) ≡ 0

data NonZeroOrNot' (M : Mat (suc m) (suc n)) : Type where
  hereIs'  : NonZeroElem M → NonZeroOrNot' M
  allZero' : M ≡ 𝟘 → NonZeroOrNot' M

findNonZero' : (M : Mat (suc m) (suc n)) → NonZeroOrNot' M
findNonZero' M =
  let  nonZero? = ∀Dec2 (λ i j → M i j ≡ 0) (λ _ _ → discreteℤ _ 0) in
  case nonZero?
  return (λ _ → NonZeroOrNot' M) of
    λ { (inl p) → allZero' (λ t i j → p i j t)
      ; (inr p) → hereIs' (nonzeroelem (p .fst , p .snd .fst) (p . snd .snd)) }


record Pivot (a : ℤ)(M : Mat (suc m) (suc n)) : Type where
  constructor comeon
  field
    coord : Fin (suc m) × Fin (suc n)
    nonDiv : ¬ a ∣ M (coord .fst) (coord .snd)

data PivotOrNot' (a : ℤ)(M : Mat (suc m) (suc n)) : Type where
  pivot   : Pivot a M → PivotOrNot' a M
  noPivot : ((i : Fin (suc m))(j : Fin (suc n)) → a ∣ M i j) → PivotOrNot' a M

findPivot' : (a : ℤ)(M : Mat (suc m) (suc n)) → PivotOrNot' a M
findPivot' a M =
  let  pivot? = ∀Dec2 (λ i j → a ∣ M i j) (λ _ _ → dec∣ _ _) in
  case pivot?
  return (λ _ → PivotOrNot' a M) of
    λ { (inl p) → noPivot p
      ; (inr p) → pivot  (comeon (p .fst , p .snd .fst) (p . snd .snd)) }


open import Cubical.Data.Bool

dec→bool : {X : Type ℓ} → Dec X → Bool
dec→bool (yes _) = true
dec→bool (no  _) = false

a' = dec→bool (dec∣ 3 10)

open QuotRem

c = bézout 9 10 .gcd


b = findNonZero (toMat3 0 0 0 0 0 0 0 0 1)


M3 = toNum2 (getMat (smithStep (toMat2 0 0 0 0)))

M4 = toNum2 (getMat (smithStep (λ zero zero → 0)))

M5 = toNum2 (getMat (smithStep (toMat2 1 0 1 0)))

M6 = toNum2 (getMat (smithStep (toMat2 1 1 0 0)))

M7 = toNum2 (getMat (smithStep (toMat2 1 0 0 0)))

M8 = toNum2 (getMat (smithStep (toMat2 0 0 0 1)))

M9 = toNum3 ((swapPivot one one BB) .sim .result)
