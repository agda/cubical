{-# OPTIONS --safe #-}
{-
  This is inspired by/copied from:
  https://github.com/agda/agda-stdlib/blob/master/src/Tactic/MonoidSolver.agda

  Boilerplate code for calling the ring solver is constructed automatically
  with agda's reflection features.
-}
module Cubical.Tactics.NatSolver.Reflection where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Functions.Logic

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Nat
open import Cubical.Data.FinData using () renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Bool
open import Cubical.Data.Bool.SwitchStatement
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_) public

open import Cubical.Tactics.NatSolver.NatExpression
open import Cubical.Tactics.NatSolver.Solver

open EqualityToNormalform renaming (solve to natSolve)
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


  firstVisibleArg : List (Arg Term) → Maybe Term
  firstVisibleArg [] = nothing
  firstVisibleArg (varg x ∷ l) = just x
  firstVisibleArg (x ∷ l) = firstVisibleArg l

  {-
    If the solver needs to be applied during equational reasoning,
    the right hand side of the equation to solve cannot be given to
    the solver directly. The folllowing function extracts this term y
    from a more complex expression as in:
      x ≡⟨ solve ... ⟩ (y ≡⟨ ... ⟩ z ∎)
  -}
  getRhs : Term → Maybe Term
  getRhs reasoningToTheRight@(def n xs) =
    if n == (quote _∎)
    then firstVisibleArg xs
    else (if n == (quote _≡⟨_⟩_)
         then firstVisibleArg xs
         else nothing)
  getRhs _ = nothing


  private
    solverCallAsTerm : Arg Term → Term → Term → Term
    solverCallAsTerm varList lhs rhs =
      def
         (quote natSolve)
         (varg lhs ∷ varg rhs
           ∷ varList
           ∷ varg (def (quote refl) []) ∷ [])

  solverCallWithLambdas : ℕ → List VarInfo → Term → Term → Term
  solverCallWithLambdas n varInfos lhs rhs =
    encloseWithIteratedLambda
      (map VarInfo.varName varInfos)
      (solverCallAsTerm (variableList (rev varInfos)) lhs rhs)
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
      solverCallAsTerm (variableList (rev varIndices)) lhs rhs
      where
        variableList : List ℕ → Arg Term
        variableList [] = varg (con (quote emptyVec) [])
        variableList (varIndex ∷ varIndices)
          = varg (con (quote _∷vec_) (varg (var (varIndex) []) ∷ (variableList varIndices) ∷ []))



module pr {n : ℕ} where
  0' : Expr n
  0' = K 0

  1' : Expr n
  1' = K 1

module _ where
  open pr

  `0` : List (Arg Term) → Term
  `0` [] = def (quote 0') []
  `0` (varg fstcring ∷ xs) = `0` xs
  `0` (harg _ ∷ xs) = `0` xs
  `0` _ = unknown

  `1` : List (Arg Term) → Term
  `1` [] = def (quote 1') []
  `1` (varg fstcring ∷ xs) = `1` xs
  `1` (harg _ ∷ xs) = `1` xs
  `1` _ = unknown

  mutual

    `_·_` : List (Arg Term) → Term
    `_·_` (harg _ ∷ xs) = `_·_` xs
    `_·_` (varg x ∷ varg y ∷ []) =
      con
        (quote _·'_) (varg (buildExpression x) ∷ varg (buildExpression y) ∷ [])
    `_·_` _ = unknown

    `_+_` : List (Arg Term) → Term
    `_+_` (harg _ ∷ xs) = `_+_` xs
    `_+_` (varg x ∷ varg y ∷ []) =
      con
        (quote _+'_) (varg (buildExpression x) ∷ varg (buildExpression y) ∷ [])
    `_+_` _ = unknown

    K' : List (Arg Term) → Term
    K' xs = con (quote K) xs

    finiteNumberAsTerm : ℕ → Term
    finiteNumberAsTerm ℕ.zero = con (quote fzero) []
    finiteNumberAsTerm (ℕ.suc n) = con (quote fsuc) (varg (finiteNumberAsTerm n) ∷ [])

    buildExpression : Term → Term
    buildExpression (var index _) = con (quote ∣) (varg (finiteNumberAsTerm index) ∷ [])
    buildExpression t@(lit n) = K' (varg t ∷ [])
    buildExpression t@(def n xs) =
      switch (n ==_) cases
        case (quote _·_) ⇒ `_·_` xs   break
        case (quote _+_) ⇒ `_+_` xs   break
        default⇒ (K' xs)
    buildExpression t@(con n xs) =
      switch (n ==_) cases
        case (quote _·_) ⇒ `_·_` xs   break
        case (quote _+_) ⇒ `_+_` xs   break
        default⇒ (K' xs)
    buildExpression t = unknown

  toAlgebraExpression : Maybe (Term × Term) → Maybe (Term × Term)
  toAlgebraExpression nothing = nothing
  toAlgebraExpression (just (lhs , rhs)) = just (buildExpression lhs , buildExpression rhs)

private
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

  solve-macro : Term → TC Unit
  solve-macro hole =
    do
      hole′ ← inferType hole >>= normalise
      just (varInfos , equation) ← returnTC (getVarsAndEquation hole′)
        where
          nothing
            → typeError (strErr "Something went wrong when getting the variable names in "
                           ∷ termErr hole′ ∷ [])
      just (lhs , rhs) ← returnTC (toAlgebraExpression (getArgs equation))
        where
          nothing
            → typeError(
                strErr "Error while trying to build ASTs for the equation " ∷
                termErr equation ∷ [])
      let solution = solverCallWithLambdas (length varInfos) varInfos lhs rhs
      unify hole solution

macro
  solve : Term → TC _
  solve = solve-macro
