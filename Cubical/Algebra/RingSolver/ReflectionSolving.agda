{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.ReflectionSolving where

open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic

open import Agda.Builtin.Reflection hiding (Type)

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Bool

open import Cubical.Algebra.RingSolver.AlgebraExpression
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.RingSolver.RawAlgebra
open import Cubical.Algebra.RingSolver.IntAsRawRing
open import Cubical.Algebra.RingSolver.CommRingSolver renaming (solve to ringSolve)


private
  variable
    ℓ : Level

getArgs : Term → Maybe (Term × Term)
getArgs (def _ xs) = go xs
  where
  go : List (Arg Term) → Maybe (Term × Term)
  go (varg x ∷ varg y ∷ []) = just (x , y)
  go (x ∷ xs)               = go xs
  go _                      = nothing
getArgs _ = nothing

constructSolution : Term → Term → Term → Term
constructSolution R lhs rhs = def (quote ringSolve) (varg R ∷ varg lhs ∷ varg rhs ∷ [])

_==_ = primQNameEquality
{-# INLINE _==_ #-}

module pr (R : CommRing {ℓ}) where
  private
    νR = CommRing→RawℤAlgebra R

  open CommRingStr (snd R)

  0' : Expr ℤAsRawRing (fst R) 1
  0' = K 1

  is0 : Name → Bool
  is0 n = (quote CommRingStr.0r) == n

  1' : Expr ℤAsRawRing (fst R) 1
  1' = K 1

  is1 : Name → Bool
  is1 n = (quote CommRingStr.1r) == n

module _ (cring : Term) where
  private
    νR = def (quote CommRing→RawℤAlgebra) (varg cring ∷ [])

  open pr

  mutual
    `0` : List (Arg Term) → Term
    `0` [] = con (quote 0') (varg cring ∷ [])
    `0` _ = unknown

    `1` : List (Arg Term) → Term
    `1` [] = con (quote 1') (varg cring ∷ [])
    `1` _ = unknown

    `_·_` : List (Arg Term) → Term
    `_·_` (varg x ∷ varg y ∷ []) =
      con
        (quote _·'_) (varg (buildExpression x) ∷ varg (buildExpression y) ∷ [])
    `_·_` _ = unknown

    `_+_` : List (Arg Term) → Term
    `_+_` (varg x ∷ varg y ∷ []) =
      con
        (quote _+'_) (varg (buildExpression x) ∷ varg (buildExpression y) ∷ [])
    `_+_` _ = unknown

    K' : List (Arg Term) → Term
    K' xs = con (quote K) xs

    buildExpression : Term → Term
    buildExpression t@(def n xs) =
      if n == (quote CommRingStr.0r)
      then `0` xs
      else if n == (quote CommRingStr.1r)
      then `1` xs
      else if n == quote CommRingStr._·_
      then `_·_` xs
      else if n == quote CommRingStr._+_
      then `_+_` xs
      else K' xs
    buildExpression t@(con n xs) =
      if n == (quote CommRingStr.0r)
      then `0` xs
      else if n == (quote CommRingStr.1r)
      then `1` xs
      else if n == quote CommRingStr._·_
      then `_·_` xs
      else if n == quote CommRingStr._+_
      then `_+_` xs
      else K' xs
    buildExpression t = unknown

  toAlgebraExpression : Maybe (Term × Term) → Maybe (Term × Term)
  toAlgebraExpression nothing = nothing
  toAlgebraExpression (just (lhs , rhs)) = just (buildExpression lhs , buildExpression rhs)

solve-macro : Term → Term → TC _
solve-macro cring hole = do
  hole′ ← inferType hole >>= normalise
  just (lhs , rhs) ← returnTC (toAlgebraExpression cring (getArgs hole′))
    where nothing → typeError (termErr hole′ ∷ [])
  let solution = constructSolution cring lhs rhs
  unify hole solution

macro
  solve : Term → Term → TC _
  solve = solve-macro

