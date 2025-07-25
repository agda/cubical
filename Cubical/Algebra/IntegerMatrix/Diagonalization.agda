{-

This file contains a diagonalization procedure simpler than Smith normalization.
For any matrix M, it provides two invertible matrices P, Q, one diagonal matrix D and an equality M = P·D·Q.
The only difference from Smith is, the numbers in D are allowed to be arbitrary, instead of being consecutively divisible.
But it is enough to establish important properties of finitely presented abelian groups.
Also, it can be computed much more efficiently (than Smith, only).

-}
module Cubical.Algebra.IntegerMatrix.Diagonalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
  hiding   (_·_)
  renaming (_+_ to _+ℕ_ ; +-assoc to +Assocℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
  using    (m∣n→m≤n)
  renaming (∣-trans to ∣ℕ-trans ; ∣-refl to ∣-reflℕ)
open import Cubical.Data.Int
  hiding   (_+_ ; _·_ ; _-_ ; -_ ; addEq)
open import Cubical.Data.Int.Divisibility
open import Cubical.Data.FinData

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit  as Unit
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Cubical.Algebra.Matrix
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.Matrix.Elementaries
open import Cubical.Algebra.IntegerMatrix.Base
open import Cubical.Algebra.IntegerMatrix.Elementaries

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int

open import Cubical.Relation.Nullary
open import Cubical.Induction.WellFounded

private
  variable
    m n k : ℕ

open CommRingStr      (ℤCommRing .snd)

open Coefficient ℤCommRing
open Sim

open ElemTransformation ℤCommRing
open ElemTransformationℤ
open SwapPivot
open RowsImproved
open ColsImproved

-- Sequence of non-zero integers

isNonZero : List ℤ → Type
isNonZero [] = Unit
isNonZero (x ∷ xs) = (¬ x ≡ 0) × isNonZero xs

isPropIsNonZero : (xs : List ℤ) → isProp (isNonZero xs)
isPropIsNonZero [] = isPropUnit
isPropIsNonZero (x ∷ xs) = isProp× (isPropΠ (λ _ → isProp⊥)) (isPropIsNonZero xs)

NonZeroList : Type
NonZeroList = Σ[ xs ∈ List ℤ ] isNonZero xs

cons : (n : ℤ)(xs : NonZeroList) → ¬ n ≡ 0 → NonZeroList
cons n (xs , _) _ .fst = n ∷ xs
cons n ([] , _) p .snd = p , tt
cons n (x ∷ xs , q) p .snd = p , q

-- Smith normal matrix

_+length_ : NonZeroList → ℕ → ℕ
xs +length n = length (xs .fst) +ℕ n

diagMat : (xs : List ℤ)(m n : ℕ) → Mat (length xs +ℕ m) (length xs +ℕ n)
diagMat [] _ _ = 𝟘
diagMat (x ∷ xs) _ _ = x ⊕ diagMat xs _ _

diagMat⊕ :
    (a : ℤ)(xs : NonZeroList){m n : ℕ}
  → (p : ¬ a ≡ 0)
  → a ⊕ diagMat (xs .fst) m n ≡ diagMat (cons a xs p .fst) m n
diagMat⊕ _ _ _ = refl

-- Diagonal matrix with non-zero diagonal elements
-- Notice that we allow non-square matrices.

record isDiagonal (M : Mat m n) : Type where
  field
    divs : NonZeroList
    rowNull : ℕ
    colNull : ℕ

    rowEq : divs +length rowNull ≡ m
    colEq : divs +length colNull ≡ n
    matEq : PathP (λ t → Mat (rowEq t) (colEq t)) (diagMat (divs .fst) rowNull colNull) M

open isDiagonal

row col : {M : Mat m n} → isDiagonal M → ℕ
row isNorm = isNorm .divs +length isNorm .rowNull
col isNorm = isNorm .divs +length isNorm .colNull

isDiagonal𝟘 : isDiagonal (𝟘 {m = m} {n = n})
isDiagonal𝟘 .divs = [] , tt
isDiagonal𝟘 {m = m} .rowNull = m
isDiagonal𝟘 {n = n} .colNull = n
isDiagonal𝟘 .rowEq = refl
isDiagonal𝟘 .colEq = refl
isDiagonal𝟘 .matEq = refl

isDiagonalEmpty : (M : Mat 0 n) → isDiagonal M
isDiagonalEmpty _ .divs = [] , tt
isDiagonalEmpty _ .rowNull = 0
isDiagonalEmpty {n = n} _ .colNull = n
isDiagonalEmpty _ .rowEq = refl
isDiagonalEmpty _ .colEq = refl
isDiagonalEmpty _ .matEq = isContr→isProp isContrEmpty _ _

isDiagonalEmptyᵗ : (M : Mat m 0) → isDiagonal M
isDiagonalEmptyᵗ _ .divs = [] , tt
isDiagonalEmptyᵗ {m = m} _ .rowNull = m
isDiagonalEmptyᵗ _ .colNull = 0
isDiagonalEmptyᵗ _ .rowEq = refl
isDiagonalEmptyᵗ _ .colEq = refl
isDiagonalEmptyᵗ _ .matEq = isContr→isProp isContrEmptyᵗ _ _


-- Induction step towards diagonalization

data DivStatus (a : ℤ)(M : Mat (suc m) (suc n)) : Type where
  badCol  : (i : Fin m)(p : ¬ a ∣ M (suc i) zero) → DivStatus a M
  badRow  : (j : Fin n)(p : ¬ a ∣ M zero (suc j)) → DivStatus a M
  allDone : ((i : Fin m) → a ∣ M (suc i) zero)
          → ((j : Fin n) → a ∣ M zero (suc j)) → DivStatus a M

divStatus : (a : ℤ)(M : Mat (suc m) (suc n)) → DivStatus a M
divStatus a M =
  let  col? = ∀Dec (λ i → a ∣ M (suc i) zero) (λ _ → dec∣ _ _)
       row? = ∀Dec (λ j → a ∣ M zero (suc j)) (λ _ → dec∣ _ _) in
  case col?
  return (λ _ → DivStatus a M) of λ
  { (inr p) → badCol (p .fst) (p .snd)
  ; (inl p) →
      case row?
      return (λ _ → DivStatus a M) of λ
      { (inr q) → badRow (q .fst) (q .snd)
      ; (inl q) → allDone p q }}

record DiagStep (M : Mat (suc m) (suc n)) : Type where
  field
    sim : Sim M

    firstColClean : (i : Fin m) → sim .result (suc i) zero ≡ 0
    firstRowClean : (j : Fin n) → sim .result zero (suc j) ≡ 0

    nonZero : ¬ sim .result zero zero ≡ 0

open DiagStep

simDiagStep : {M : Mat (suc m) (suc n)}(sim : Sim M) → DiagStep (sim .result) → DiagStep M
simDiagStep simM diag .sim = compSim simM (diag .sim)
simDiagStep _    diag .firstColClean = diag .firstColClean
simDiagStep _    diag .firstRowClean = diag .firstRowClean
simDiagStep _    diag .nonZero = diag .nonZero

private
  diagStep-helper :
      (M : Mat (suc m) (suc n))
    → (p : ¬ M zero zero ≡ 0)(h : Norm (M zero zero))
    → (div? : DivStatus (M zero zero) M)
    → DiagStep M
  diagStep-helper M p (acc ind) (badCol i q) =
    let improved = improveRows M p
        normIneq =
          ind _ (stDivIneq p q (improved .div zero) (improved .div (suc i)))
    in  simDiagStep (improved .sim)
                    (diagStep-helper _ (improved .nonZero) normIneq (divStatus _ _))
  diagStep-helper M p (acc ind) (badRow j q) =
    let improved = improveCols M p
        normIneq =
          ind _ (stDivIneq p q (improved .div zero) (improved .div (suc j)))
    in  simDiagStep (improved .sim)
                    (diagStep-helper _ (improved .nonZero) normIneq (divStatus _ _))
  diagStep-helper M p (acc ind) (allDone div₁ div₂) =
    let improveColM = improveCols M p
        invCol = bézoutRows-inv _ p div₂
        divCol = (λ i → transport (λ t → invCol t zero ∣ invCol t (suc i)) (div₁ i))
        improveRowM = improveRows (improveColM .sim .result) (improveColM .nonZero)
        invCol = bézoutRows-inv _ (improveColM .nonZero) divCol
    in  record
        { sim = compSim (improveColM .sim) (improveRowM .sim)
        ; firstColClean = improveRowM .vanish
        ; firstRowClean = (λ j → (λ t → invCol (~ t) (suc j)) ∙ improveColM .vanish j)
        ; nonZero = improveRowM .nonZero }

  diagStep-getStart : (M : Mat (suc m) (suc n)) → NonZeroOrNot M → DiagStep M ⊎ (M ≡ 𝟘)
  diagStep-getStart _ (allZero p) = inr p
  diagStep-getStart M (hereIs i j p) =
    let swapM = swapPivot i j M
        swapNonZero = (λ r → p (swapM .swapEq ∙ r))
        diagM = diagStep-helper _ swapNonZero (<-wellfounded _) (divStatus _ _)
    in  inl (simDiagStep (swapM .sim) diagM)

diagStep : (M : Mat (suc m) (suc n)) → DiagStep M ⊎ (M ≡ 𝟘)
diagStep _ = diagStep-getStart _ (findNonZero _)


-- The diagonalization

record Diag (M : Mat m n) : Type where
  field
    sim : Sim M
    isdiag : isDiagonal (sim .result)

open Diag

simDiag : {M : Mat m n}(sim : Sim M) → Diag (sim .result) → Diag M
simDiag simM diag .sim = compSim simM (diag .sim)
simDiag _ diag .isdiag = diag .isdiag

diag𝟘 : Diag (𝟘 {m = m} {n = n})
diag𝟘 .sim    = idSim _
diag𝟘 .isdiag = isDiagonal𝟘

diagEmpty : (M : Mat 0 n) → Diag M
diagEmpty _ .sim    = idSim _
diagEmpty M .isdiag = isDiagonalEmpty M

diagEmptyᵗ : (M : Mat m 0) → Diag M
diagEmptyᵗ _ .sim    = idSim _
diagEmptyᵗ M .isdiag = isDiagonalEmptyᵗ M

decompDiagStep :
    (M : Mat (suc m) (suc n))(step : DiagStep M)
  → step .sim .result ≡ step .sim .result zero zero ⊕ sucMat (step .sim .result)
decompDiagStep M step t zero zero = step .sim .result zero zero
decompDiagStep M step t zero (suc j) = step .firstRowClean j t
decompDiagStep M step t (suc i) zero = step .firstColClean i t
decompDiagStep M step t (suc i) (suc j) = step .sim .result (suc i) (suc j)

consIsDiagonal :
    (a : ℤ)(M : Mat m n)
  → (p : ¬ a ≡ 0)
  → isDiagonal M → isDiagonal (a ⊕ M)
consIsDiagonal a _ p diag .divs = cons a (diag .divs) p
consIsDiagonal _ _ _ diag .rowNull = diag .rowNull
consIsDiagonal _ _ _ diag .colNull = diag .colNull
consIsDiagonal _ _ _ diag .rowEq = (λ t → suc (diag .rowEq t))
consIsDiagonal _ _ _ diag .colEq = (λ t → suc (diag .colEq t))
consIsDiagonal a _ _ diag .matEq = (λ t → a ⊕ diag .matEq t)

diagReduction :
    (a : ℤ)(M : Mat m n)
  → (p : ¬ a ≡ 0)
  → Diag M → Diag (a ⊕ M)
diagReduction a _ _ diag .sim = ⊕Sim a (diag .sim)
diagReduction a _ p diag .isdiag = consIsDiagonal a _ p (diag .isdiag)


-- The Existence of Diagonalization

diagonalize : (M : Mat m n) → Diag M
diagonalize {m = 0} = diagEmpty
diagonalize {m = suc m} {n = 0} = diagEmptyᵗ
diagonalize {m = suc m} {n = suc n} M = helper (diagStep _)
  where
  helper : DiagStep M ⊎ (M ≡ 𝟘) → Diag M
  helper (inr p) = subst Diag (sym p) diag𝟘
  helper (inl stepM) =
    let sucM = sucMat (stepM .sim .result)
        diagM = diagReduction _ _ (stepM .nonZero) (diagonalize sucM)
    in  simDiag (compSim (stepM .sim) (≡Sim (decompDiagStep _ stepM))) diagM
