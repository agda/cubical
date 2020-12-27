{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.ReflectionSolving where

open import Cubical.Foundations.Prelude

open import Agda.Builtin.Reflection hiding (Type)

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat

open import Cubical.Algebra.RingSolver.CommRingSolver renaming (solve to ringSolve)

data CRingNames : Type _ where

cringNames : Term → TC CRingNames
cringNames cring = {!!}

getArgs : Term → Maybe (Term × Term)
getArgs (def _ xs) = go xs
  where
  go : List (Arg Term) → Maybe (Term × Term)
  go (varg x ∷ varg y ∷ []) = just (x , y)
  go (x ∷ xs)               = go xs
  go _                      = nothing
getArgs _ = nothing

constructSolution : Term → Term → Term → CRingNames → Term
constructSolution R lhs rhs names = def (quote ringSolve) (varg R ∷ varg lhs ∷ varg rhs ∷ {!!})

toAlgebraExpression : Maybe (Term × Term) → Maybe (Term × Term)
toAlgebraExpression nothing = nothing
toAlgebraExpression (just (lhs , rhs)) = {!!}

solve-macro : Term → Term → TC _
solve-macro cring hole = do
  hole′ ← inferType hole >>= normalise
  names ← cringNames cring
  just (lhs , rhs) ← returnTC (toAlgebraExpression (getArgs hole′))
    where nothing → typeError (termErr hole′ ∷ [])
  let solution = {!!} -- constructSolution cring lhs rhs names
  unify hole solution

macro
  solve : Term → Term → TC _
  solve = solve-macro

_ = solve ℕ
