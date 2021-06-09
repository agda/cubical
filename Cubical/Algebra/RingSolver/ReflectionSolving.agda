{-# OPTIONS --safe #-}
{-
  This is inspired by/copied from:
  https://github.com/agda/agda-stdlib/blob/master/src/Tactic/MonoidSolver.agda
-}
module Cubical.Algebra.RingSolver.ReflectionSolving where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Functions.Logic

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Int.Base hiding (abs)
open import Cubical.Data.Int using (fromNegℤ; fromNatℤ)
open import Cubical.Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.FinData using () renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool
open import Cubical.Data.Bool.SwitchStatement
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_) public

open import Cubical.Algebra.RingSolver.AlgebraExpression
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.RawAlgebra
open import Cubical.Algebra.RingSolver.IntAsRawRing
open import Cubical.Algebra.RingSolver.CommRingSolver renaming (solve to ringSolve)

private
  variable
    ℓ : Level

  _==_ = primQNameEquality
  {-# INLINE _==_ #-}

  record VarInfo : Type ℓ-zero where
    field
      varName : String
      varType : Arg Term
      index : ℕ

  getArgs : Term → Maybe (Term × Term)
  getArgs (def n xs) =
    if n == (quote PathP)
    then go xs
    else nothing
      where
      go : List (Arg Term) → Maybe (Term × Term)
      go (varg x ∷ varg y ∷ []) = just (x , y)
      go (x ∷ xs)               = go xs
      go _                      = nothing
  getArgs _ = nothing

  constructSolution : ℕ → List VarInfo → Term → Term → Term → Term
  constructSolution n varInfos R lhs rhs =
    encloseWithIteratedLambda (map VarInfo.varName varInfos) solverCall
    where
      encloseWithIteratedLambda : List String → Term → Term
      encloseWithIteratedLambda (varName ∷ xs) t = lam visible (abs varName (encloseWithIteratedLambda xs t))
      encloseWithIteratedLambda [] t = t

      variableList : List VarInfo → Arg Term
      variableList [] = varg (con (quote emptyVec) [])
      variableList (varInfo ∷ varInfos)
        = varg (con (quote _∷vec_) (varg (var (VarInfo.index varInfo) []) ∷ (variableList varInfos) ∷ []))

      solverCall = def
         (quote ringSolve)
         (varg R ∷ varg lhs ∷ varg rhs
           ∷ variableList (rev varInfos)
           ∷ varg (def (quote refl) []) ∷ [])

module pr (R : CommRing ℓ) {n : ℕ} where
  private
    νR = CommRing→RawℤAlgebra R

  open CommRingStr (snd R)

  0' : Expr ℤAsRawRing (fst R) n
  0' = K 0

  1' : Expr ℤAsRawRing (fst R) n
  1' = K 1

module _ (cring : Term) where
  private
    νR = def (quote CommRing→RawℤAlgebra) (varg cring ∷ [])

  open pr

  mutual
    `0` : List (Arg Term) → Term
    `0` [] = def (quote 0') (varg cring ∷ [])
    `0` (varg fstcring ∷ xs) = `0` xs
    `0` (harg _ ∷ xs) = `0` xs
    `0` _ = unknown

    `1` : List (Arg Term) → Term
    `1` [] = def (quote 1') (varg cring ∷ [])
    `1` (varg fstcring ∷ xs) = `1` xs
    `1` (harg _ ∷ xs) = `1` xs
    `1` _ = unknown

    `_·_` : List (Arg Term) → Term
    `_·_` (harg _ ∷ xs) = `_·_` xs
    `_·_` (varg _ ∷ varg x ∷ varg y ∷ []) =
      con
        (quote _·'_) (varg (buildExpression x) ∷ varg (buildExpression y) ∷ [])
    `_·_` _ = unknown

    `_+_` : List (Arg Term) → Term
    `_+_` (harg _ ∷ xs) = `_+_` xs
    `_+_` (varg _ ∷ varg x ∷ varg y ∷ []) =
      con
        (quote _+'_) (varg (buildExpression x) ∷ varg (buildExpression y) ∷ [])
    `_+_` _ = unknown

    `-_` : List (Arg Term) → Term
    `-_` (harg _ ∷ xs) = `-_` xs
    `-_` (varg _ ∷ varg x ∷ []) =
      con
        (quote -'_) (varg (buildExpression x) ∷ [])
    `-_` _ = unknown

    K' : List (Arg Term) → Term
    K' xs = con (quote K) xs

    finiteNumberAsTerm : ℕ → Term
    finiteNumberAsTerm ℕ.zero = con (quote fzero) []
    finiteNumberAsTerm (ℕ.suc n) = con (quote fsuc) (varg (finiteNumberAsTerm n) ∷ [])

    buildExpression : Term → Term
    buildExpression (var index _) = con (quote ∣) (varg (finiteNumberAsTerm index) ∷ [])
    buildExpression t@(def n xs) =
      switch (n ==_) cases
        case (quote CommRingStr.0r)  ⇒ `0` xs     break
        case (quote CommRingStr.1r)  ⇒ `1` xs     break
        case (quote CommRingStr._·_) ⇒ `_·_` xs   break
        case (quote CommRingStr._+_) ⇒ `_+_` xs   break
        case (quote (CommRingStr.-_))  ⇒ `-_` xs    break
        default⇒ (K' xs)
    buildExpression t@(con n xs) =
      switch (n ==_) cases
        case (quote CommRingStr.0r)  ⇒ `0` xs     break
        case (quote CommRingStr.1r)  ⇒ `1` xs     break
        case (quote CommRingStr._·_) ⇒ `_·_` xs   break
        case (quote CommRingStr._+_) ⇒ `_+_` xs   break
        case (quote (CommRingStr.-_))  ⇒ `-_` xs    break
        default⇒ (K' xs)
    buildExpression t = unknown

  toAlgebraExpression : Maybe (Term × Term) → Maybe (Term × Term)
  toAlgebraExpression nothing = nothing
  toAlgebraExpression (just (lhs , rhs)) = just (buildExpression lhs , buildExpression rhs)

private
  adjustDeBruijnIndex : (n : ℕ) → Term → Term
  adjustDeBruijnIndex n (var k args) = var (k +ℕ n) args
  adjustDeBruijnIndex n _ = unknown

  getVarsAndEquation : Term → Maybe (List VarInfo × Term)
  getVarsAndEquation t =
    let
      (rawVars , equationTerm) = extractVars t
      maybeVars = addIndices (length rawVars) rawVars
    in map-Maybe (_, equationTerm) maybeVars
    where
          extractVars : Term → List (String × Arg Term) × Term
          extractVars (pi argType (abs varName t)) with extractVars t
          ...                                         | xs , equation = (varName , argType) ∷ xs , equation
          extractVars equation = [] , equation

          addIndices : ℕ → List (String × Arg Term) → Maybe (List VarInfo)
          addIndices ℕ.zero         []        = just []
          addIndices (ℕ.suc countVar) ((varName , argType) ∷ list) =
            map-Maybe (λ varList → record { varName = varName ; varType = argType ; index = countVar }
                                   ∷ varList)
                      (addIndices countVar list)
          addIndices _ _ = nothing

  solve-macro : Term → Term → TC Unit
  solve-macro cring hole = do
    hole′ ← inferType hole >>= normalise
    just (varInfos , equation) ← returnTC (getVarsAndEquation hole′)
      where
        nothing
          → typeError (strErr "Something went wrong when getting the variable names in "
                         ∷ termErr hole′ ∷ [])
    adjustedCring ← returnTC (adjustDeBruijnIndex (length varInfos) cring)
    just (lhs , rhs) ← returnTC (toAlgebraExpression adjustedCring (getArgs equation))
      where
        nothing
          → typeError(
              strErr "Error while trying to buils ASTs for the equation " ∷
              termErr equation ∷ [])
    let solution = constructSolution (length varInfos) varInfos adjustedCring lhs rhs
    unify hole solution

macro
  solve : Term → Term → TC _
  solve = solve-macro

fromℤ : (R : CommRing ℓ) → ℤ → fst R
fromℤ = scalar
