module Cubical.Algebra.MonoidSolver.ReflectionSolving where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Functions.Logic

open import Agda.Builtin.Reflection
  hiding (Type) renaming (normalise to normalizeTerm)
--open import Agda.Builtin.String

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Nat using (ℕ)
--open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Vec using (Vec; lookup)

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.MonoidSolver.NaiveSolving

private
  variable
    ℓ : Level

_==_ = primQNameEquality
{-# INLINE _==_ #-}

module _ (M : Monoid ℓ) where
  open MonoidStr (snd M)

  getArgs : Term → Maybe (Term × Term)
  getArgs (def _ xs) = go xs
    where
    go : List (Arg Term) → Maybe (Term × Term)
    go (varg x ∷ varg y ∷ []) = just (x , y)
    go (x ∷ xs)               = go xs
    go _                      = nothing
  getArgs _ = nothing

  record MonoidNames : Type where ---wirklich ohne ℓ ???
    field
      is-· : Name → Bool
      is-ε : Name → Bool

  buildMatcher : Name → Maybe Name → Name → Bool
  buildMatcher n nothing  x = n == x
  buildMatcher n (just m) x = n == x or m == x

  findMonoidNames : Term → TC MonoidNames
  findMonoidNames mon = do
    ·-altName ← normalizeTerm (def (quote _·_) PrependingTwoArgs) --(2 ⋯⟅∷⟆ mon ⟨∷⟩ []))
    ε-altName ← normalizeTerm (def (quote ε) PrependingTwoArgs) --(2 ⋯⟅∷⟆ mon ⟨∷⟩ []))
    returnTC record
      { is-· = buildMatcher (quote _·_) (getName ·-altName)
      ; is-ε = buildMatcher (quote ε)   (getName ε-altName)
      }
    where
      PrependingTwoArgs = unknown h∷ unknown h∷ mon v∷ []

      getName : Term → Maybe Name
      getName (con c args) = just c
      getName (def f args) = just f
      getName _            = nothing

  module BuildingExpressions (names : MonoidNames) where
    open MonoidNames names

    ″ε″ : Term
    ″ε″ = con (quote ε⊗) [] --quote ε⊗ ⟨ con ⟩ []

    V′ : Term → Term
    V′ t = con (quote V) (t v∷ [])

    mutual
      ″·″ : List (Arg Term) → Term
      ″·″ (x v∷ y v∷ []) = con (quote _⊗_) (buildExpr x v∷ buildExpr y v∷ [])
      ″·″ (x ∷ xs)         = ″·″ xs
      ″·″ _                = unknown

      buildExpr : Term → Term
      buildExpr t@(def n xs) =
        if is-· n
          then ″·″ xs
        else if is-ε n
          then ″ε″
        else V′ t
      buildExpr t@(con n xs) =
        if is-· n
          then ″·″ xs
        else if is-ε n
          then ″ε″
        else V′ t
      buildExpr t = con (quote V) (t v∷ [])

{-
  constructSolution : Term → MonoidNames → Term → Term → Term
  constructSolution mon names lhs rhs =
    quote Monoid.trans ⟨ def ⟩ 2 ⋯⟅∷⟆ mon ⟨∷⟩
      (quote Monoid.sym ⟨ def ⟩ 2 ⋯⟅∷⟆ mon ⟨∷⟩
        (quote homo ⟨ def ⟩ 2 ⋯⟅∷⟆ mon ⟨∷⟩ buildExpr names lhs ⟨∷⟩ []) ⟨∷⟩ [])
      ⟨∷⟩
      (quote homo ⟨ def ⟩ 2 ⋯⟅∷⟆ mon ⟨∷⟩ buildExpr names rhs ⟨∷⟩ []) ⟨∷⟩
      []

  ----------------------------------------------------------------------
  -- Macro
  ----------------------------------------------------------------------

  solve-macro : Term → Term → TC _
  solve-macro mon hole = do
    hole′ ← inferType hole >>= normalise
    names ← findMonoidNames mon
    just (lhs , rhs) ← returnTC (getArgs hole′)
      where nothing → typeError (termErr hole′ ∷ [])
    let soln = constructSoln mon names lhs rhs
    unify hole soln

  macro
    solve : Term → Term → TC _
    solve = solve-macro
-}
