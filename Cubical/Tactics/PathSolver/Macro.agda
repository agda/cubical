{-

This module provides macros for manipulating cubical terms using reflection machinery. It includes utilities to transform terms by exposing functions from the `CongComp` module and simplify the construction of `hcomps`.

Usage examples for these macros are available in the `Cubical.Tactics.PathSolver.MacroExamples` module.

-}

{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.Macro where

open import Cubical.Foundations.Function

open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma

open import Agda.Builtin.String

open import Cubical.Reflection.Base renaming (v to 𝒗)
open import Cubical.Reflection.Sugar
import Agda.Builtin.Reflection as R

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.QuoteCubical
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.CuTerm

open import Cubical.Tactics.Reflection.CuTerm public using (⁇)

open import Cubical.Tactics.PathSolver.CongComp

{-

### Macros Exposing Helpers from `CongComp` Module

These macros expose helpers from the `CongComp` module, offering broader application beyond the `NSolver` and `MonoidalSolver` macros. They support terms of arbitrary dimensions and complex interval expressions.

- **Usage**: Apply these macros in a context where interval variables are present. Paths and n-cubes must be applied to the respective dimensions.
- **Functionality**:
  - **`cong$` Macro**: Transforms the given term by bringing all `hcomps` to the top, so all functions are applied "all the way down" through the `hcomps`. This process happens iteratively for all subterms.
  - **`cong$-fill` Macro**: Provides a filler path from the initial term to the term produced by `cong$`. Assumes there is an additional interval variable in the context not present in the processed term, used as the filling direction.

-}

macro
 cong$ : R.Term → R.Term → R.TC Unit
 cong$ t h = do
   ty ← R.inferType t
   t ← normaliseWithType ty t
   cc ← getCuCtx
   let dim = length cc
   co ← R.getContext
   cu ← R.inContext (drop dim co) $ appCongs dim
           <$> quoteCuTerm (just (dropVars.rv dim zero ty)) dim (t)
   let r = ToTerm.toTerm cc cu
   R.unify r h <|> R.typeError [ r ]ₑ



macro
 cong$-fill : R.Term → R.Term → R.TC Unit
 cong$-fill t h = do
   ty ← R.inferType t
   t ← normaliseWithType ty t
   cc ← getCuCtx
   let dim = predℕ (length cc)
   co ← R.getContext
   cu ← R.inContext (drop (suc dim) co) $ fillCongs 100 dim
           <$> quoteCuTerm nothing --(just (dropVars.rv (suc dim) zero ty))
                          dim (dropVar dim t)
   let r = ToTerm.toTerm cc cu

   R.unify r h --<|> R.typeError [ r ]ₑ



makeH? : R.Term → R.Term → R.TC String
makeH? iT eT = do
  cuCtx ← getCuCtx
  let dim = length cuCtx
  fE ← iFxprFromSpec dim iT

  cuCtx ← L.map (map-snd (const nothing)) ∘S take dim <$> R.getContext
  (((hcoFromIExpr dim fE eT) >>= codeGen.ppCT'' false dim cuCtx 10) >>= R.formatErrorParts)

 where
 iFxprFromSpec : ℕ → R.Term → R.TC FExpr
 iFxprFromSpec dim t =
   (R.unquoteTC {A = ℕ} t <⊎> extractIExprM t)
     <|> (R.typeError $
         "Wrong parameter!"
         ∷nl [ "pass either ℕ or Interval Expr as first argument!" ]ₑ)
   >>= pure ∘S ⊎.rec (allSubFacesOfSfDim dim ∘S min (predℕ dim))
                     ((_++fe (allSubFacesOfSfDim dim 0)) ∘S I→F)

{-

The following macros are designed to facilitate the construction of homogeneous `hcomps` given a face expression. They simplify the process of writing nested `hcomp`'s .

## Macros Overview

 **Usage**: These macros must be called in a context where interval variables are in scope.
 **Arguments**:
   **First Argument**:
    - A face expression (e.g., `(i ∨ k) ∨ (~k ∧ ~j)`) or
    - A natural number that specifies the dimension. This will generate a face expression consisting of all faces of the specified dimension from available interval variables.
   **Second Argument**:
    - A term to serve as a value for all generated cells, or
    - The `⁇` symbol (`\??`) to insert holes into all cells for further editing.
-}

macro


 -- Produces the term directly in the hole where it is called (via `C-c C-m` in emacs).
 -- Note: This macro may have issues correctly introducing holes in the face expressions.
 h? : R.Term → R.Term → R.Term → R.TC Unit
 h? iT eT h = do
  src ← makeH? iT eT
  unifyFromString src h


 -- Generates a slightly better-looking term compared to `h?`.
 -- The result is printed to the AgdaInfo buffer,
 -- and users must manually copy it to the desired location in the code.
 h?' : R.Term → R.Term → R.Term → R.TC Unit
 h?' iT eT _ = do
  src ← makeH? iT eT
  R.typeError [ indent ' ' 8 src ]ₑ
