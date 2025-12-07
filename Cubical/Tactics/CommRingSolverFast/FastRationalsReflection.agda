module Cubical.Tactics.CommRingSolverFast.FastRationalsReflection where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function
open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)
open import Cubical.Reflection.Sugar

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Int.Fast.Base hiding (abs; _-_)
open import Cubical.Data.Int.Fast using (fromNegℤ; fromNatℤ)
open import Cubical.Data.Nat using (ℕ; discreteℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool
open import Cubical.Data.Bool.SwitchStatement
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_)

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing

open import Cubical.Tactics.CommRingSolverFast.AlgebraExpression

open import Cubical.Tactics.CommRingSolverFast.Decidable

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Error
open import Cubical.Algebra.CommRing.Instances.Rationals.Fast
open import Cubical.Data.Rationals.Fast as ℚ
import Cubical.Data.NatPlusOne as NatPlusOne
import Cubical.HITs.SetQuotients as SetQuotient


open DecCommRingSolver ℚCommRing ℚ.discreteℚ

private
  variable
    ℓ : Level


  wrdℚ : ∀ {a} {A : Type a} → TC A → TC A
  wrdℚ = withReduceDefs
     (false , ((quote ℚ._+_) ∷ (quote (ℚ.-_)) ∷ (quote ℚ._·_) ∷ []))


  solverCallAsTerm : Arg Term → Term → Term → Term → Term
  solverCallAsTerm varList lhs rhs ihr =
    def
       (quote solve)
       (lhs v∷ rhs
         v∷ varList
         ∷ ihr v∷  [])

  variableList : Vars → Arg Term
  variableList [] = varg (con (quote emptyVec) [])
  variableList (t ∷ ts)
    = varg (con (quote _∷vec_) (t v∷ (variableList ts) ∷ []))





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


  buildExpression t@(con (quote SetQuotient.[_]) _) =
   returnTC (((λ _ → con (quote K) v[ t ]) , []))

  buildExpression (def (quote ℚ._+_) xs) = `_+_` xs
  buildExpression (def (quote ℚ._·_) xs) = `_·_` xs
  buildExpression (def (quote ℚ.-_) xs) = `-_` xs
  
  buildExpression t@(def _ _) = returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ [])
  buildExpression t@(meta _ _) = returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ [])

  buildExpression t = errorOut' t


  toAlgebraExpression : Term × Term → TC (Term × Term × Vars)
  toAlgebraExpression (lhs , rhs) = do
      r1 ← buildExpression lhs
      r2 ← buildExpression rhs
      vars ← returnTC (appendWithoutRepetition (snd r1) (snd r2))
      returnTC (
        let ass : VarAss
            ass n = indexOf n vars
        in (fst r1 ass , fst r2 ass , vars ))

  toAlgebraExpressionLHS : Term → TC (Term × Vars)
  toAlgebraExpressionLHS lhs = do
      (e , vars) ← buildExpression lhs

      returnTC (
        let ass : VarAss
            ass n = indexOf n vars
        in (e ass , vars ))


  mkIHR : ∀ {n} → (e₁ e₂ : IteratedHornerForms n) → (Maybe Term)
  mkIHR (const _) (const _) = just (def (quote ℚ.eqℚ) (def (quote refl) [] v∷ []))
  mkIHR 0H 0H = just unknown
  mkIHR (e₁ ·X+ e₂) (e₁' ·X+ e₂') = do
    p₁ ← mkIHR e₁ e₁'
    p₂ ← mkIHR e₂ e₂'
    just (con (quote _,_) (p₁ v∷ v[ p₂ ]))
  mkIHR _ _ = nothing
  
  solve!-macro : Term → TC Unit
  solve!-macro hole = 
    do
        
      goal ← wrdℚ $ inferType hole >>= normalise
      
      wrdℚ $ wait-for-type goal
      just (lhs , rhs) ← wrdℚ $ get-boundary goal
        where
          nothing
            → typeError(strErr "The CommRingSolver failed to parse the goal "
                               ∷ termErr goal ∷ [])

      (lhs' , rhs' , vars) ← wrdℚ $  toAlgebraExpression (lhs , rhs)

      lhs* ← normalize <$> unquoteTC {A = RExpr (length vars)} lhs'
      rhs* ← normalize <$> unquoteTC {A = RExpr (length vars)} rhs'
      
      (just ihr) ← pure (mkIHR {length vars} lhs* rhs*)
        where nothing → do
             lhs*tm ← quoteTC lhs* >>= normalise
             rhs*tm ← quoteTC rhs* >>= normalise
             typeError ("normalised, not equal! :" ∷nl lhs*tm ∷nl rhs*tm ∷ₑ [])
      
      let solution = solverCallAsTerm (variableList vars) lhs' rhs' ihr
       
      unify hole solution

macro
  ℚ!! : Term → TC _
  ℚ!! = solve!-macro
