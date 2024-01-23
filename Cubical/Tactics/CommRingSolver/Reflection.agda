{-# OPTIONS --safe #-}
module Cubical.Tactics.CommRingSolver.Reflection where

open import Cubical.Foundations.Prelude hiding (Type)

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Int.Base hiding (abs; _-_)
open import Cubical.Data.Int using (fromNegℤ; fromNatℤ)
open import Cubical.Data.Nat using (ℕ; discreteℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool
open import Cubical.Data.Bool.SwitchStatement
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_)

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing

open import Cubical.Tactics.CommRingSolver.AlgebraExpression
open import Cubical.Tactics.CommRingSolver.RawAlgebra
open import Cubical.Tactics.CommRingSolver.IntAsRawRing
open import Cubical.Tactics.CommRingSolver.Solver renaming (solve to ringSolve)

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities

private
  variable
    ℓ : Level

  record RingNames : Type where
    field
      is0 : Name → Bool
      is1 : Name → Bool
      is· : Name → Bool
      is+ : Name → Bool
      is- : Name → Bool

  getName : Term → Maybe Name
  getName (con c args) = just c
  getName (def f args) = just f
  getName _            = nothing

  buildMatcher : Name → Maybe Name → Name → Bool
  buildMatcher n nothing  x = n == x
  buildMatcher n (just m) x = n == x or m == x

  findRingNames : Term → TC RingNames
  findRingNames cring =
    let cringStr = (def (quote snd) (cring v∷ [])) v∷ []
    in do
      0altName ← normalise (def (quote CommRingStr.0r) cringStr)
      1altName ← normalise (def (quote CommRingStr.1r) cringStr)
      ·altName ← normalise (def (quote CommRingStr._·_) cringStr)
      +altName ← normalise (def (quote CommRingStr._+_) cringStr)
      -altName ← normalise (def (quote (CommRingStr.-_)) cringStr)
      returnTC record {
          is0 = buildMatcher (quote CommRingStr.0r) (getName 0altName) ;
          is1 = buildMatcher (quote CommRingStr.1r) (getName 1altName) ;
          is· = buildMatcher (quote CommRingStr._·_) (getName ·altName) ;
          is+ = buildMatcher (quote CommRingStr._+_) (getName +altName) ;
          is- = buildMatcher (quote (CommRingStr.-_)) (getName -altName)
        }

  solverCallAsTerm : Term → Arg Term → Term → Term → Term
  solverCallAsTerm R varList lhs rhs =
    def
       (quote ringSolve)
       (R v∷ lhs v∷ rhs
         v∷ varList
         ∷ (def (quote refl) []) v∷ [])

  solverCallWithVars : ℕ → Vars → Term → Term → Term → Term
  solverCallWithVars n vars R lhs rhs =
      solverCallAsTerm R (variableList vars) lhs rhs
      where
        variableList : Vars → Arg Term
        variableList [] = varg (con (quote emptyVec) [])
        variableList (t ∷ ts)
          = varg (con (quote _∷vec_) (t v∷ (variableList ts) ∷ []))

module pr (R : CommRing ℓ) {n : ℕ} where
  open CommRingStr (snd R)

  0' : Expr ℤAsRawRing (fst R) n
  0' = K 0

  1' : Expr ℤAsRawRing (fst R) n
  1' = K 1

module CommRingReflection (cring : Term) (names : RingNames) where
  open pr
  open RingNames names

  `0` : List (Arg Term) → TC (Template × Vars)
  `0` [] = returnTC (((λ _ → def (quote 0') (cring v∷ [])) , []))
  `0` (fstcring v∷ xs) = `0` xs
  `0` (_ h∷ xs) = `0` xs
  `0` something = errorOut something

  `1` : List (Arg Term) → TC (Template × Vars)
  `1` [] = returnTC ((λ _ → def (quote 1') (cring v∷ [])) , [])
  `1` (fstcring v∷ xs) = `1` xs
  `1` (_ h∷ xs) = `1` xs
  `1` something = errorOut something

  buildExpression : Term → TC (Template × Vars)

  op2 : Name → Term → Term → TC (Template × Vars)
  op2 op x y = do
    r1 ← buildExpression x
    r2 ← buildExpression y
    returnTC ((λ ass → con op (fst r1 ass v∷ fst r2 ass v∷ [])) ,
             appendWithoutRepetition (snd r1) (snd r2))

  op1 : Name → Term → TC (Template × Vars)
  op1 op x = do
    r1 ← buildExpression x
    returnTC ((λ ass → con op (fst r1 ass v∷ [])) , snd r1)

  `_·_` : List (Arg Term) → TC (Template × Vars)
  `_·_` (_ h∷ xs) = `_·_` xs
  `_·_` (x v∷ y v∷ []) = op2 (quote _·'_) x y
  `_·_` (_ v∷ x v∷ y v∷ []) = op2 (quote _·'_) x y
  `_·_` ts = errorOut ts

  `_+_` : List (Arg Term) → TC (Template × Vars)
  `_+_` (_ h∷ xs) = `_+_` xs
  `_+_` (x v∷ y v∷ []) = op2 (quote _+'_) x y
  `_+_` (_ v∷ x v∷ y v∷ []) = op2 (quote _+'_) x y
  `_+_` ts = errorOut ts

  `-_` : List (Arg Term) → TC (Template × Vars)
  `-_` (_ h∷ xs) = `-_` xs
  `-_` (x v∷ []) = op1 (quote -'_) x
  `-_` (_ v∷ x v∷ []) = op1 (quote -'_) x
  `-_` ts = errorOut ts

  polynomialVariable : Maybe ℕ → Term
  polynomialVariable n = con (quote ∣) (finiteNumberAsTerm n v∷ [])

  -- buildExpression : Term → Template × Vars
  buildExpression v@(var _ _) =
    returnTC ((λ ass → polynomialVariable (ass v)) ,
             v ∷ [])
  buildExpression t@(def n xs) =
    switch (λ f → f n) cases
      case is0 ⇒ `0` xs         break
      case is1 ⇒ `1` xs         break
      case is· ⇒ `_·_` xs       break
      case is+ ⇒ `_+_` xs       break
      case is- ⇒ `-_` xs        break
      default⇒ (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))
  buildExpression t@(con n xs) =
    switch (λ f → f n) cases
      case is0 ⇒ `0` xs         break
      case is1 ⇒ `1` xs         break
      case is· ⇒ `_·_` xs       break
      case is+ ⇒ `_+_` xs       break
      case is- ⇒ `-_` xs        break
      default⇒ (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))
  buildExpression t = errorOut' t
  -- there should be cases for variables which are functions, those should be detectable by having visible args
  -- there should be cases for definitions (with arguments)

  toAlgebraExpression : Term × Term → TC (Term × Term × Vars)
  toAlgebraExpression (lhs , rhs) = do
      r1 ← buildExpression lhs
      r2 ← buildExpression rhs
      vars ← returnTC (appendWithoutRepetition (snd r1) (snd r2))
      returnTC (
        let ass : VarAss
            ass n = indexOf n vars
        in (fst r1 ass , fst r2 ass , vars ))

private
  checkIsRing : Term → TC Term
  checkIsRing ring = checkType ring (def (quote CommRing) (unknown v∷ []))

  solve!-macro : Term → Term → TC Unit
  solve!-macro uncheckedCommRing hole =
    do
      commRing ← checkIsRing uncheckedCommRing
      goal ← inferType hole >>= normalise
      names ← findRingNames commRing

      wait-for-type goal
      just (lhs , rhs) ← get-boundary goal
        where
          nothing
            → typeError(strErr "The CommRingSolver failed to parse the goal "
                               ∷ termErr goal ∷ [])

      (lhs' , rhs' , vars) ← CommRingReflection.toAlgebraExpression commRing names (lhs , rhs)
      let solution = solverCallWithVars (length vars) vars commRing lhs' rhs'
      unify hole solution

macro
  solve! : Term → Term → TC _
  solve! = solve!-macro
