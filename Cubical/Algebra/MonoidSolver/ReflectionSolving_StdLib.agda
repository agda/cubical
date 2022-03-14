module Cubical.Algebra.MonoidSolver.ReflectionSolving_StdLib where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Functions.Logic

open import Agda.Builtin.Reflection
  hiding (Type) renaming (normalise to normalizeTerm)

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Vec using (Vec; lookup)

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.MonoidSolver.NaiveSolving_StdLib

private
  variable
    ℓ : Level

_==_ = primQNameEquality
{-# INLINE _==_ #-}


----------------------------------------------------------------------
-- Relflection helper
----------------------------------------------------------------------

infixr 5 _⋯h∷_
_⋯h∷_ : ℕ → List (Arg Term) → List (Arg Term)
ℕ.zero ⋯h∷ xs = xs
ℕ.suc n ⋯h∷ xs = harg unknown ∷ (n ⋯h∷ xs)
{-# INLINE _⋯h∷_ #-}



getArgs : Term → Maybe (Term × Term)
getArgs (def _ xs) = go xs
  where
  go : List (Arg Term) → Maybe (Term × Term)
  go (varg x ∷ varg y ∷ []) = just (x , y)
  go (x ∷ xs)               = go xs
  go _                      = nothing
getArgs _ = nothing

record MonoidNames : Type where
  field
    is-· : Name → Bool
    is-ε : Name → Bool

buildMatcher : Name → Maybe Name → Name → Bool
buildMatcher n nothing  x = n == x
buildMatcher n (just m) x = n == x or m == x



findMonoidNames : Term → TC MonoidNames
findMonoidNames mon = do
  ·-altName ← normalizeTerm (def (quote MonoidStr._·_) (2 ⋯h∷ varg mon ∷ []))
  ε-altName ← normalizeTerm (def (quote MonoidStr.ε) (2 ⋯h∷ varg mon ∷ []))
  returnTC record
    { is-· = buildMatcher (quote MonoidStr._·_) (getName ·-altName)
    ; is-ε = buildMatcher (quote MonoidStr.ε)   (getName ε-altName)
    }
  where
    getName : Term → Maybe Name
    getName (con c args) = just c
    getName (def f args) = just f
    getName _            = nothing

module _ (names : MonoidNames) where
  open MonoidNames names

  ″ε″ : Term
  ″ε″ = con (quote ε⊗) []

  V′ : Term → Term
  V′ t = con (quote V) (varg t ∷ [])

  mutual
    ″·″ : List (Arg Term) → Term
    ″·″ (varg x ∷ varg y ∷ []) =
      con
        (quote _⊗_) (varg (buildExpr x) ∷ varg (buildExpr y) ∷ [])
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
    buildExpr t = con (quote V) (varg t ∷ [])

constructSoln : Term → MonoidNames → Term → Term → Term
constructSoln mon names lhs rhs =
  def (quote _∙_) (2 ⋯h∷ mon
    v∷
    (def (quote sym) (2 ⋯h∷ varg mon ∷
       (def (quote isEqualToNormalform) (2 ⋯h∷ varg mon ∷ (varg (buildExpr names lhs)) ∷ [])) v∷ []))
    v∷
    (def (quote isEqualToNormalform) (2 ⋯h∷ varg mon ∷ (varg (buildExpr names rhs)) ∷ []))
    v∷
    [])

----------------------------------------------------------------------
-- Macro
----------------------------------------------------------------------

solve-macro : Term → Term → TC _
solve-macro mon hole = do
  hole′ ← inferType hole >>= normalizeTerm
  names ← findMonoidNames mon
  just (lhs , rhs) ← returnTC (getArgs hole′)
    where nothing → typeError (termErr hole′ ∷ [])
  let soln = constructSoln mon names lhs rhs
  unify hole soln

macro
  solve : Term → Term → TC _
  solve = solve-macro

{-
module test (M : Monoid ℓ) where
  open MonoidStr (snd M)

  test : ε ≡ ε
  test = solve (snd M)
-}
