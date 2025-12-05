module Cubical.Tactics.CommRingSolverFast.IntPlusReflection where

open import Cubical.Foundations.Prelude hiding (Type)

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Int.Fast.Base hiding (abs; _-_)
open import Cubical.Data.Int.Fast using (fromNegℤ; fromNatℤ)
import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Nat using (ℕ; discreteℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool
open import Cubical.Data.Bool.SwitchStatement
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_)

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing

open import Cubical.Tactics.CommRingSolverFast.AlgebraExpression
open import Cubical.Tactics.CommRingSolverFast.RawAlgebra
open import Cubical.Tactics.CommRingSolverFast.IntAsRawRing
open import Cubical.Tactics.CommRingSolverFast.IntSolver renaming (solve to ringSolve)

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities

import Cubical.Data.NatPlusOne as NPO

import Cubical.Data.Nat as ℕ

open import Cubical.Algebra.CommRing.Instances.Int.Fast

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

  solverCallAsTerm : Arg Term → Term → Term → Term
  solverCallAsTerm varList lhs rhs =
    def
       (quote ringSolve)
       (lhs v∷ rhs
         v∷ varList
         ∷ (def (quote refl) []) v∷ [])

  solverCallWithVars : ℕ → Vars → Term → Term → Term
  solverCallWithVars n vars lhs rhs =
      solverCallAsTerm (variableList vars) lhs rhs
      where
        variableList : Vars → Arg Term
        variableList [] = varg (con (quote emptyVec) [])
        variableList (t ∷ ts)
          = varg (con (quote _∷vec_) (t v∷ (variableList ts) ∷ []))

  normaliserCallAsTerm : Arg Term → Term → Term
  normaliserCallAsTerm varList lhs =
    def
       (quote normaliseRing)
       (lhs v∷ varList ∷ [])

  normaliserCallWithVars : ℕ → Vars → Term → Term
  normaliserCallWithVars n vars lhs =
      normaliserCallAsTerm (variableList vars) lhs
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
  
  Fuel = ℕ

  buildExpression : Fuel → Term → TC (Template × Vars)

  op2 : Fuel → Name → Term → Term → TC (Template × Vars)
  op2 f op x y = do
    r1 ← buildExpression f x
    r2 ← buildExpression f y
    returnTC ((λ ass → con op (fst r1 ass v∷ fst r2 ass v∷ [])) ,
             appendWithoutRepetition (snd r1) (snd r2))

  op1 : Fuel → Name → Term → TC (Template × Vars)
  op1 f op x = do
    r1 ← buildExpression f x
    returnTC ((λ ass → con op (fst r1 ass v∷ [])) , snd r1)

  scalarℕ : ℕ → TC (Template × Vars)
  scalarℕ n = returnTC (((λ _ →
    con (quote K) (con (quote pos) (lit (nat n) v∷ []) v∷ [])) , []))


  `_·_` : Fuel → List (Arg Term) → TC (Template × Vars)
  `_·_` f (_ h∷ xs) = `_·_` f xs
  `_·_` f (x v∷ y v∷ []) = op2 f (quote _·'_) x y
  `_·_` f (_ v∷ x v∷ y v∷ []) = op2 f (quote _·'_) x y
  `_·_` _ ts = errorOut ts

  `_+_` : Fuel → List (Arg Term) → TC (Template × Vars)
  `_+_` f (_ h∷ xs) = `_+_` f xs
  `_+_` f (x v∷ y v∷ []) = op2 f (quote _+'_) x y
  `_+_` f (_ v∷ x v∷ y v∷ []) = op2 f (quote _+'_) x y
  `_+_` _ ts = errorOut ts

  `-_` : Fuel → List (Arg Term) → TC (Template × Vars)
  `-_` f (_ h∷ xs) = `-_` f xs
  `-_` f (x v∷ []) = op1 f (quote -'_) x
  `-_` f (_ v∷ x v∷ []) = op1 f (quote -'_) x
  `-_` _ ts = errorOut ts


  polynomialVariable : Maybe ℕ → Term
  polynomialVariable n = con (quote ∣) (finiteNumberAsTerm n v∷ [])

  buildExpressionFromNat : Fuel → Term → TC (Template × Vars)
  buildExpressionFromNatPlus : Fuel → Term → TC (Template × Vars)
  buildExpressionFromNatPlus  ℕ.zero _ = typeError [ strErr "outOfFuel" ]
  buildExpressionFromNatPlus f (def (quote NPO._·₊₁_) (x v∷ y v∷ [])) =
   do
      r1 ← buildExpressionFromNatPlus f x
      r2 ← buildExpressionFromNatPlus f y
      returnTC ((λ ass → con (quote _·'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
               appendWithoutRepetition (snd r1) (snd r2))


  buildExpressionFromNatPlus f (con (quote NPO.1+_) ((con (quote ℕ.zero) []) v∷ [])) = `1` []
  buildExpressionFromNatPlus f (con (quote NPO.1+_) ((lit (nat x)) v∷ [])) = scalarℕ (ℕ.suc x) 


  buildExpressionFromNatPlus f (con (quote NPO.1+_) (x@(var _ []) v∷ [])) =
   let t = (con (quote ℤ.pos) ((con (quote ℕ.suc) (x v∷ [] )) v∷ []))
   in (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))


  -- buildExpressionFromNatPlus (ℕ.suc f) (con (quote NPO.1+_)
  --    ((def (quote ℕ._+_) (𝒏@(def (quote NPO.ℕ₊₁.n) (n v∷ [])) v∷
  --     (def (quote ℕ._·_) ((def (quote NPO.ℕ₊₁.n) (m v∷ [])) v∷ (con (quote ℕ.suc) (𝒏* v∷ [] )) v∷ [])) v∷ [])) v∷ [])) = do
  --   unify 𝒏 𝒏*
  --   buildExpressionFromNatPlus f (def (quote NPO._·₊₁_) (m v∷ n v∷ []))


  -- buildExpressionFromNatPlus (ℕ.suc f) (con (quote NPO.1+_)
  --    ((def (quote ℕ._+_) (n v∷
  --     (def (quote ℕ._·_) (m v∷ (con (quote ℕ.suc) (n* v∷ [] )) v∷ [])) v∷ [])) v∷ [])) = do
  --   unify n n*
  --   buildExpressionFromNatPlus f (def (quote NPO._·₊₁_)
  --    (con (quote NPO.1+_) (m v∷ []) v∷
  --     con (quote NPO.1+_) (n v∷ []) v∷
  --     []))


  buildExpressionFromNatPlus (ℕ.suc f) (con (quote NPO.1+_)
     ((def (quote ℕ._+_) (n v∷
      (def (quote ℕ._·_) (m v∷ sn v∷ [])) v∷ [])) v∷ [])) = do
    unify (con (quote ℕ.suc) (n v∷ [] )) sn
    buildExpressionFromNatPlus f (def (quote NPO._·₊₁_)
     (con (quote NPO.1+_) (m v∷ []) v∷
      con (quote NPO.1+_) (n v∷ []) v∷
      []))


  buildExpressionFromNatPlus f t =
   typeError (strErr "unexpected in nbuildExpressionFromNatPlus: \n " ∷ termErr t ∷ [])
  



  buildExpressionFromNat f t@(lit (nat x)) = -- typeError (strErr "scalar: " ∷ termErr t ∷ [])
    scalarℕ x --buildExpressionFromNatLit x
  buildExpressionFromNat f (con (quote ℕ.zero) []) = `0` []
  buildExpressionFromNat f (con (quote ℕ.suc) (con (quote ℕ.zero) [] v∷ [] )) = `1` []
  buildExpressionFromNat f (con (quote ℕ.suc) (x v∷ [] )) =
    do
    debugPrint "intSolver" 20  (strErr "fromNat suc:" ∷ termErr x ∷ [])
    r1 ← `1` []
    r2 ← buildExpressionFromNat f x
    returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
             appendWithoutRepetition (snd r1) (snd r2))
  buildExpressionFromNat f (def (quote ℕ._+_) (x v∷ y v∷ [])) =
    do
    debugPrint "intSolver" 20  (strErr "buildNateExpr ℕ._+_ :" ∷ termErr x ∷ [])
    r1 ← buildExpressionFromNat f x
    r2 ← buildExpressionFromNat f y
    returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
             appendWithoutRepetition (snd r1) (snd r2))
  buildExpressionFromNat f (def (quote ℕ._·_) (x v∷ y v∷ [])) =
    do
    r1 ← buildExpressionFromNat f x
    r2 ← buildExpressionFromNat f y
    returnTC ((λ ass → con (quote _·'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
             appendWithoutRepetition (snd r1) (snd r2))
  buildExpressionFromNat f (def (quote _ℕ-_) (x v∷ (con (quote ℕ.suc) (y v∷ [] )) v∷ [])) =
    do
    r1 ← buildExpressionFromNat f x
    r2 ← do y' ← do u1 ← `1` []
                    u2 ← buildExpressionFromNat f y
                    returnTC {A = Template × Vars} ((λ ass → con (quote _+'_) (fst u1 ass v∷ fst u2 ass v∷ [])) ,
                         appendWithoutRepetition (snd u1) (snd u2))
            returnTC {A = Template × Vars} ((λ ass → con (quote -'_) (fst y' ass v∷ [])) , snd y')
    returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
             appendWithoutRepetition (snd r1) (snd r2))
  buildExpressionFromNat f t' =
   let t = (con (quote ℤ.pos) (t' v∷ []))
   in (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))


  buildExpression ℕ.zero _ = typeError [ strErr "outOfFuel" ]
  buildExpression f (def (quote ℚ.ℕ₊₁→ℤ) (x v∷ [])) =
   buildExpressionFromNatPlus f x
  buildExpression f v@(var _ _) =
    returnTC ((λ ass → polynomialVariable (ass v)) ,
             v ∷ [])
  buildExpression f t@(def n xs) =
    switch (λ f → f n) cases
      case is0 ⇒ `0` xs         break
      case is1 ⇒ `1` xs         break
      case is· ⇒ `_·_` f xs       break
      case is+ ⇒ `_+_` f xs       break
      case is- ⇒ `-_` f xs        break
      default⇒ (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))

  buildExpression f t@(con (quote ℤ.pos) (x v∷ [])) = do
    debugPrint "intSolver" 20  (strErr "buildExpr pos:" ∷ termErr x ∷ [])
    buildExpressionFromNat f x
  buildExpression f t@(con (quote ℤ.negsuc) (x v∷ [])) =
   do debugPrint "intSolver" 20  (strErr "buildExpr negsuc:" ∷ termErr x ∷ [])
      y ← do r1 ← `1` []
             r2 ← buildExpressionFromNat f x
             returnTC {A = Template × Vars} ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
                   appendWithoutRepetition (snd r1) (snd r2))
      returnTC ((λ ass → con (quote -'_) (fst y ass v∷ [])) , snd y)
  buildExpression f t@(con n xs) =
    switch (λ f → f n) cases
      case is0 ⇒ `0` xs         break
      case is1 ⇒ `1` xs         break
      case is· ⇒ `_·_` f xs       break
      case is+ ⇒ `_+_` f xs       break
      case is- ⇒ `-_` f xs        break
      default⇒ (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))
  buildExpression f t = errorOut' t
  -- there should be cases for variables which are functions, those should be detectable by having visible args
  -- there should be cases for definitions (with arguments)

  defaultFuel : Fuel
  defaultFuel = 1000

  toAlgebraExpression : Term × Term → TC (Term × Term × Vars)
  toAlgebraExpression (lhs , rhs) = do
      r1 ← buildExpression defaultFuel lhs
      r2 ← buildExpression defaultFuel rhs
      vars ← returnTC (appendWithoutRepetition (snd r1) (snd r2))
      returnTC (
        let ass : VarAss
            ass n = indexOf n vars
        in (fst r1 ass , fst r2 ass , vars ))

  toAlgebraExpressionLHS : Term → TC (Term × Vars)
  toAlgebraExpressionLHS lhs = do
      (e , vars) ← buildExpression defaultFuel lhs

      returnTC (
        let ass : VarAss
            ass n = indexOf n vars
        in (e ass , vars ))


private
  checkIsRing : Term → TC Term
  checkIsRing ring = checkType ring (def (quote CommRing) (unknown v∷ []))

  normalise!-macro : Term → TC Unit
  normalise!-macro hole =
      withReduceDefs
     (false , ((quote ℕ._·_) ∷
        (quote ℕ._+_) ∷ (quote _+_) ∷ (quote (-_)) ∷ (quote _·_) ∷ (quote _ℕ-_) ∷ []))
    do
      commRing ← checkIsRing (def (quote ℤCommRing) [])
      goal ← inferType hole >>= normalise
      names ← findRingNames commRing

      -- wait-for-type goal
      just (lhs , rhs) ← get-boundary goal
      
        where
          nothing
            → typeError(strErr "The CommRingSolver failed to parse the goal "
                               ∷ termErr goal ∷ [])

      (lhs' , vars) ← CommRingReflection.toAlgebraExpressionLHS commRing names lhs
      -- printVars "intSolverVars" vars
      let solution = normaliserCallWithVars (length vars) vars lhs'
      unify hole solution


solve!-macro : Term → TC Unit
solve!-macro hole =
    withReduceDefs
   (false , ((quote ℕ._·_) ∷
      (quote ℕ._+_) ∷ (quote _+_) ∷ (quote (-_)) ∷ (quote _·_) ∷ (quote _ℕ-_)
       -- ∷ []))
       ∷ (quote NPO._+₁_) ∷ (quote NPO._·₊₁_) ∷ (quote NPO.ℕ₊₁→ℕ) ∷ (quote ℚ.ℕ₊₁→ℤ) ∷ []))
  do
    commRing ← checkIsRing (def (quote ℤCommRing) [])
    goal ← inferType hole >>= normalise
    names ← findRingNames commRing

    wait-for-type goal
    just (lhs , rhs) ← get-boundary goal
      where
        nothing
          → typeError(strErr "The CommRingSolver failed to parse the goal "
                             ∷ termErr goal ∷ [])
    debugPrint "intSolverGoal" 20 (strErr "LHS:\n" ∷ termErr lhs ∷ [])
    debugPrint "intSolverGoal" 20 (strErr "RHS:\n" ∷ termErr rhs ∷ [])
    (lhs' , rhs' , vars) ← CommRingReflection.toAlgebraExpression commRing names (lhs , rhs)
    -- printVars "intSolverVars" vars
    -- typeError []
    -- debugPrint "intSolverGoal" 20 (strErr "LHS':\n" ∷ termErr lhs' ∷ [])
    -- debugPrint "intSolverGoal" 20 (strErr "RHS':\n" ∷ termErr rhs' ∷ [])
    let solution = solverCallWithVars (length vars) vars lhs' rhs'
    unify hole solution


macro
  ℤ! : Term → TC _
  ℤ! = solve!-macro

  ℤ↓ : Term → TC _
  ℤ↓ = normalise!-macro
