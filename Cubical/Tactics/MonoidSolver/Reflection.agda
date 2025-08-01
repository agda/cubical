
module Cubical.Tactics.MonoidSolver.Reflection where

open import Cubical.Foundations.Prelude hiding (Type)

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.FinData using () renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_) public

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.CommMonoid.Base
open import Cubical.Tactics.MonoidSolver.Solver renaming (solve to naiveSolve)
open import Cubical.Tactics.MonoidSolver.CommSolver renaming (solve to naiveCommSolve)
open import Cubical.Tactics.MonoidSolver.MonoidExpression

private
  variable
    ℓ : Level

module ReflectionSolver (op unit solver : Name) where

  _==_ = primQNameEquality
  {-# INLINE _==_ #-}

  record VarInfo : Type ℓ-zero where
    field
      varName : String
      varType : Arg Term
      index : ℕ

  {-
    `getLastTwoArgsOf` maps a term 'def n (z₁ ∷ … ∷ zₙ ∷ x ∷ y ∷ [])' to the pair '(x,y)'
    non-visible arguments are ignored.
  -}
  getLastTwoArgsOf : Name → Term → Maybe (Term × Term)
  getLastTwoArgsOf n' (def n xs) =
    if n == n'
    then go xs
    else nothing
      where
      go : List (Arg Term) → Maybe (Term × Term)
      go (varg x ∷ varg y ∷ []) = just (x , y)
      go (x ∷ xs)               = go xs
      go _                      = nothing
  getLastTwoArgsOf n' _ = nothing

  {-
    `getArgs` maps a term 'x ≡ y' to the pair '(x,y)'
  -}
  getArgs : Term → Maybe (Term × Term)
  getArgs = getLastTwoArgsOf (quote PathP)

  private
    solverCallAsTerm : Term → Arg Term → Term → Term → Term
    solverCallAsTerm M varList lhs rhs =
      def
         solver
         (varg M ∷ varg lhs ∷ varg rhs
           ∷ varList
           ∷ varg (def (quote refl) []) ∷ [])

  solverCallWithLambdas : ℕ → List VarInfo → Term → Term → Term → Term
  solverCallWithLambdas n varInfos M lhs rhs =
    encloseWithIteratedLambda
      (map VarInfo.varName varInfos)
      (solverCallAsTerm M (variableList (rev varInfos)) lhs rhs)
    where
      encloseWithIteratedLambda : List String → Term → Term
      encloseWithIteratedLambda (varName ∷ xs) t = lam visible (abs varName (encloseWithIteratedLambda xs t))
      encloseWithIteratedLambda [] t = t

      variableList : List VarInfo → Arg Term
      variableList [] = varg (con (quote emptyVec) [])
      variableList (varInfo ∷ varInfos)
        = varg (con (quote _∷vec_) (varg (var (VarInfo.index varInfo) []) ∷ (variableList varInfos) ∷ []))

  solverCallByVarIndices : ℕ → List ℕ → Term → Term → Term → Term
  solverCallByVarIndices n varIndices R lhs rhs =
      solverCallAsTerm R (variableList (rev varIndices)) lhs rhs
      where
        variableList : List ℕ → Arg Term
        variableList [] = varg (con (quote emptyVec) [])
        variableList (varIndex ∷ varIndices)
          = varg (con (quote _∷vec_) (varg (var (varIndex) []) ∷ (variableList varIndices) ∷ []))

  module _ (monoid : Term) where

    `ε⊗` : Term
    `ε⊗` = con (quote ε⊗) []

    mutual

      `_⊗_` : List (Arg Term) → Term
      `_⊗_` (harg _ ∷ xs) = `_⊗_` xs
      `_⊗_` (varg _ ∷ varg x ∷ varg y ∷ []) =
        con
          (quote _⊗_) (varg (buildExpression x) ∷ varg (buildExpression y) ∷ [])
      `_⊗_` _ = unknown

      finiteNumberAsTerm : ℕ → Term
      finiteNumberAsTerm ℕ.zero = con (quote fzero) []
      finiteNumberAsTerm (ℕ.suc n) = con (quote fsuc) (varg (finiteNumberAsTerm n) ∷ [])

      buildExpression : Term → Term
      buildExpression (var index _) = con (quote ∣) (varg (finiteNumberAsTerm index) ∷ [])
      buildExpression t@(def n xs) =
        if (n == op)
          then `_⊗_` xs
        else if (n == unit)
          then `ε⊗`
        else
          unknown
      buildExpression t = unknown


    toMonoidExpression : Maybe (Term × Term) → Maybe (Term × Term)
    toMonoidExpression nothing = nothing
    toMonoidExpression (just (lhs , rhs)) = just (buildExpression lhs , buildExpression rhs)

  adjustDeBruijnIndex : (n : ℕ) → Term → Term
  adjustDeBruijnIndex n (var k args) = var (k + n) args
  adjustDeBruijnIndex n _ = unknown

  extractVarIndices : Maybe (List Term) → Maybe (List ℕ)
  extractVarIndices (just ((var index _) ∷ l)) with extractVarIndices (just l)
  ... | just indices = just (index ∷ indices)
  ... | nothing = nothing
  extractVarIndices (just []) = just []
  extractVarIndices _ = nothing

  getVarsAndEquation : Term → Maybe (List VarInfo × Term)
  getVarsAndEquation t =
    let
      (rawVars , equationTerm) = extractVars t
      maybeVars = addIndices (length rawVars) rawVars
    in map-Maybe (_, equationTerm) maybeVars
    where
          extractVars : Term → List (String × Arg Term) × Term
          extractVars (pi argType (abs varName t)) with extractVars t
          ...                                         | xs , equation
                                                        = (varName , argType) ∷ xs , equation
          extractVars equation = [] , equation

          addIndices : ℕ → List (String × Arg Term) → Maybe (List VarInfo)
          addIndices ℕ.zero         []        = just []
          addIndices (ℕ.suc countVar) ((varName , argType) ∷ list) =
            map-Maybe (λ varList → record { varName = varName ; varType = argType ; index = countVar }
                                   ∷ varList)
                      (addIndices countVar list)
          addIndices _ _ = nothing

  toListOfTerms : Term → Maybe (List Term)
  toListOfTerms (con c []) = if (c == (quote [])) then just [] else nothing
  toListOfTerms (con c (varg t ∷ varg s ∷ args)) with toListOfTerms s
  ... | just terms = if (c == (quote _∷_)) then just (t ∷ terms) else nothing
  ... | nothing = nothing
  toListOfTerms (con c (harg t ∷ args)) = toListOfTerms (con c args)
  toListOfTerms _ = nothing

  solve-macro : Term → Term → TC Unit
  solve-macro monoid hole =
    do
      hole′ ← inferType hole >>= normalise
      just (varInfos , equation) ← returnTC (getVarsAndEquation hole′)
        where
          nothing
            → typeError (strErr "Something went wrong when getting the variable names in "
                           ∷ termErr hole′ ∷ [])
      {-
        The call to the monoid solver will be inside a lamba-expression.
        That means, that we have to adjust the deBruijn-indices of the variables in 'monoid'
      -}
      adjustedMonoid ← returnTC (adjustDeBruijnIndex (length varInfos) monoid)
      just (lhs , rhs) ← returnTC (toMonoidExpression adjustedMonoid (getArgs equation))
        where
          nothing
            → typeError(
                strErr "Error while trying to build ASTs for the equation " ∷
                termErr equation ∷ [])
      let solution = solverCallWithLambdas (length varInfos) varInfos adjustedMonoid lhs rhs
      unify hole solution

macro
  solveMonoid : Term → Term → TC _
  solveMonoid = ReflectionSolver.solve-macro (quote MonoidStr._·_) (quote MonoidStr.ε) (quote naiveSolve)

  solveCommMonoid : Term → Term → TC _
  solveCommMonoid = ReflectionSolver.solve-macro (quote CommMonoidStr._·_) (quote CommMonoidStr.ε) (quote naiveCommSolve)
