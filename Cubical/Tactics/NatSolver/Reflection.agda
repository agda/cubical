{-# OPTIONS --safe #-}
{-
  This is inspired by/copied from:
  https://github.com/agda/agda-stdlib/blob/master/src/Tactic/MonoidSolver.agda
  and the 1lab.

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
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Bool.SwitchStatement
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_) public

open import Cubical.Tactics.NatSolver.NatExpression
open import Cubical.Tactics.NatSolver.Solver

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities

open EqualityToNormalform renaming (solve to natSolve)
private
  variable
    ℓ : Level

  private
    solverCallAsTerm : Arg Term → Term → Term → Term
    solverCallAsTerm varList lhs rhs =
      def
         (quote natSolve)
         (varg lhs ∷ varg rhs
           ∷ varList
           ∷ varg (def (quote refl) []) ∷ [])

  solverCallWithVars : ℕ → Vars → Term → Term → Term
  solverCallWithVars n vars lhs rhs =
      solverCallAsTerm (variableList vars) lhs rhs
      where
        variableList : Vars → Arg Term
        variableList [] = varg (con (quote emptyVec) [])
        variableList (t ∷ ts)
          = varg (con (quote _∷vec_) (t v∷ (variableList ts) ∷ []))

module pr {n : ℕ} where
  0' : Expr n
  0' = K 0

  1' : Expr n
  1' = K 1

module NatSolverReflection where
  open pr

  buildExpression : Term → TC (Template × Vars)

  op2 : Name → Term → Term → TC (Template × Vars)
  op2 op x y = do
    r1 ← buildExpression x
    r2 ← buildExpression y
    returnTC ((λ ass → con op (fst r1 ass v∷ fst r2 ass v∷ [])) ,
             appendWithoutRepetition (snd r1) (snd r2))

  `_·_` : List (Arg Term) → TC (Template × Vars)
  `_·_` (_ h∷ xs) = `_·_` xs
  `_·_` (x v∷ y v∷ []) = op2 (quote _·'_) x y
  `_·_` ts = errorOut ts

  `_+_` : List (Arg Term) → TC (Template × Vars)
  `_+_` (_ h∷ xs) = `_+_` xs
  `_+_` (x v∷ y v∷ []) = op2 (quote _+'_) x y
  `_+_` ts = errorOut ts

  `1+_` : List (Arg Term) → TC (Template × Vars)
  `1+_` (x v∷ []) = do
    r1 ← buildExpression x
    returnTC ((λ ass → con (quote _+'_) ((def (quote 1') []) v∷ fst r1 ass v∷ [])) ,
              snd r1)
  `1+_` ts = errorOut ts

  K' : List (Arg Term) → TC (Template × Vars)
  K' xs = returnTC ((λ _ → con (quote K) xs) , [])

  polynomialVariable : Maybe ℕ → Term
  polynomialVariable (just n) = con (quote ∣) (finiteNumberAsTerm (just n) v∷ [])
  polynomialVariable nothing = unknown

  buildExpression v@(var _ _) =
      returnTC ((λ ass → polynomialVariable (ass v)) ,
           v ∷ [])
  buildExpression t@(lit n) = K' (t v∷ [])
  buildExpression t@(def n xs) =
    switch (n ==_) cases
      case (quote _·_) ⇒ `_·_` xs   break
      case (quote _+_) ⇒ `_+_` xs   break
      default⇒ (K' xs)
  buildExpression t@(con n xs) =
    switch (n ==_) cases
      case (quote suc) ⇒ `1+_` xs   break
      default⇒ (K' xs)
  buildExpression t = errorOut' t

  toNatExpression : Term × Term → TC (Term × Term × Vars)
  toNatExpression (lhs , rhs) = do
      r1 ← buildExpression lhs
      r2 ← buildExpression rhs
      vars ← returnTC (appendWithoutRepetition (snd r1) (snd r2))
      returnTC (
        let ass : VarAss
            ass n = indexOf n vars
        in (fst r1 ass , fst r2 ass , vars ))

private

  solve!-macro : Term → TC Unit
  solve!-macro hole =
    do
      goal ← inferType hole >>= normalise

      just (lhs , rhs) ← get-boundary goal
        where
          nothing
            → typeError(strErr "The NatSolver failed to parse the goal "
                               ∷ termErr goal ∷ [])

      (lhs' , rhs' , vars) ← NatSolverReflection.toNatExpression (lhs , rhs)
      let solution = solverCallWithVars (length vars) vars lhs' rhs'
      unify hole solution

macro
  solveℕ! : Term → TC _
  solveℕ! = solve!-macro
