{-# OPTIONS --cubical --no-import-sorts --safe #-}
{-
  This is inspired by/copied from:
  https://github.com/agda/agda-stdlib/blob/master/src/Tactic/MonoidSolver.agda
-}
module Cubical.Algebra.RingSolver.ReflectionSolving where

open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic

open import Agda.Builtin.Reflection hiding (Type)

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Int hiding (_+'_; _-_; -_)
open import Cubical.Data.Bool
open import Cubical.Data.Bool.SwitchStatement
open import Cubical.Data.Vec using () renaming ([] to emptyVec)

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

constructSolution : Term → Term → Term → Term
constructSolution R lhs rhs =
  def
    (quote ringSolve)
    (varg R ∷ varg lhs ∷ varg rhs
      ∷ varg (con (quote emptyVec) [])
      ∷ varg (def (quote refl) []) ∷ [])

module pr (R : CommRing {ℓ}) where
  private
    νR = CommRing→RawℤAlgebra R

  open CommRingStr (snd R) hiding (_-_)

  0' : Expr ℤAsRawRing (fst R) 0
  0' = K 0

  1' : Expr ℤAsRawRing (fst R) 0
  1' = K 1

  disamb- : fst R → fst R
  disamb- x = - x

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

    buildExpression : Term → Term
    buildExpression t@(def n xs) =
      switch (λ n' → n == n') cases
        case (quote CommRingStr.0r)  ⇒ `0` xs     break
        case (quote CommRingStr.1r)  ⇒ `1` xs     break
        case (quote CommRingStr._·_) ⇒ `_·_` xs   break
        case (quote CommRingStr._+_) ⇒ `_+_` xs   break
        case (quote disamb-)         ⇒ `-_` xs   break
        default⇒ (K' xs)
    buildExpression t@(con n xs) =
      switch (λ n' → n == n') cases
        case (quote CommRingStr.0r)  ⇒ `0` xs     break
        case (quote CommRingStr.1r)  ⇒ `1` xs     break
        case (quote CommRingStr._·_) ⇒ `_·_` xs   break
        case (quote CommRingStr._+_) ⇒ `_+_` xs   break
        case (quote disamb-)         ⇒ `-_` xs   break
        default⇒ (K' xs)
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

