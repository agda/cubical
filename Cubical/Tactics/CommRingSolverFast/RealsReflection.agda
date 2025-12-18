module Cubical.Tactics.CommRingSolverFast.RealsReflection where

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

open import Cubical.Tactics.CommRingSolverFast.OverDecidable

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables hiding (addWithoutRepetition;appendWithoutRepetition)
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Error
open import Cubical.Algebra.CommRing.Instances.Rationals.Fast
open import Cubical.Data.Rationals.Fast as ℚ
import Cubical.Data.NatPlusOne as NatPlusOne
import Cubical.HITs.SetQuotients as SetQuotient
open import Cubical.HITs.CauchyReals.Base
import Cubical.HITs.CauchyReals.Multiplication as ℝ
import Cubical.HITs.CauchyReals.Lipschitz as ℝ
import Cubical.HITs.CauchyReals.Continuous as ℝ
import Cubical.HITs.CauchyReals.Order as ℝ
open import Cubical.Tactics.CommRingSolverFast.RationalsReflection using (doNotUnfoldsℚ)

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Float
open import Agda.Builtin.Word
open import Agda.Builtin.Char
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_ ; _*_ to _*ℕ_ ; _+_ to _+ℕ_)


open DecCommRingSolver ℚCommRing ℚ.discreteℚ ℝ.ℝring ℝ.ℚ→ℝHom

module _ (dbg : Bool) where



  private
    _=N_ = primQNameEquality
    _=M_ = primMetaEquality

    _=L_ : Literal → Literal → Bool
    nat n =L nat m = n =ℕ m
    word64 n =L word64 m = primWord64ToNat n =ℕ primWord64ToNat m
    float x =L float y = primFloatEquality x y
    char c =L char c' = primCharEquality c c'
    string s =L string s' = primStringEquality s s'
    name x =L name y = x =N y
    meta x =L meta y = x =M y
    _ =L _ = false

    compareVargs : List (Arg Term) → List (Arg Term) → Bool

    _=T_ : Term → Term → Bool  -- this should be a TC, since it should error out sometimes
    var index args =T var index' args' = (index =ℕ index') and compareVargs args args'
    con c args =T con c' args'   = (c =N c') and compareVargs args args'
    def f args =T def f' args'   = (f =N f') and compareVargs args args'
    lit l =T lit l'              = l =L l'
    meta x args =T meta x' args' = (x =M x') and compareVargs args args'
    lam _ (abs _ x) =T lam _ (abs _ x') = x =T x'
    _ =T _                       = false  -- this should be fixed

  compareVargs [] [] = true
  compareVargs (x v∷ l) (x' v∷ l') = (x =T x') and compareVargs l l'
  compareVargs (_ h∷ l) (_ h∷ l') = compareVargs l l' -- ignore hargs, not sure this is good
  compareVargs _ _ = false

  addWithoutRepetition : Term → Vars → Vars
  addWithoutRepetition t l@(t' ∷ l') = if (t =T t') then l else t' ∷ addWithoutRepetition t l'
  addWithoutRepetition t []      = t ∷ []

  appendWithoutRepetition : Vars → Vars → Vars
  appendWithoutRepetition (x ∷ l) l' = appendWithoutRepetition l (addWithoutRepetition x l')
  appendWithoutRepetition [] l' = l'


  debugPrint' : String → ℕ → List ErrorPart → TC Unit
  debugPrint' = if dbg then debugPrint else (λ _ _ _ → pure _)


  wrdℚ : ∀ {a} {A : Type a} → TC A → TC A
  wrdℚ = withReduceDefs
     (false , ((quote ℚ._+_) ∷ (quote (ℚ.-_)) ∷ (quote ℚ._·_) ∷ quote ℝ.fromLipschitz ∷ doNotUnfoldsℚ))


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

-- (returnTC (((λ _ → con (quote K) v[ t ]) , [])))

  -- buildExpressionFrom-P/Q' : Term → Term → (TC (Template × Vars))
  -- buildExpressionFrom-P/Q' = {!!}

  isConstℕ? : Term → Bool
  isConstℕ? (con _ []) = true
  isConstℕ? (lit _) = true
  isConstℕ? (con _ v[ x ]) = isConstℕ? x
  isConstℕ? _ = false

  isConstℤ? : Term → Bool
  isConstℤ? (con _ v[ n ]) = isConstℕ? n
  isConstℤ? _ = false



  isScalarℚ? : List (Arg Term) → Bool
  isScalarℚ? (_ h∷ xs) = isScalarℚ? xs
  isScalarℚ? v[ con (quote _,_) xs ] = isScalarℚ? xs
  isScalarℚ? (p v∷ v[ con (quote NatPlusOne.1+_) v[ q ] ]) = isConstℤ? p and isConstℕ? q
  isScalarℚ? _ = false

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


  buildExpression (con (quote rat) v[ t@(con (quote SetQuotient.[_]) x) ]) =
   if isScalarℚ? x then (returnTC (((λ _ → con (quote K) v[ t ]) , [])))
     else (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))
    -- Cubical.Data.Maybe.rec (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))
    --   (idfun _)
    --   (buildExpressionFrom-P/Q x)
   -- returnTC (((λ _ → con (quote K) v[ t ]) , []))


  buildExpression (def (quote ℝ._+ᵣ_) xs) = `_+_` xs
  buildExpression (def (quote ℝ._·ᵣ_) xs) = `_·_` xs
  buildExpression (def (quote ℝ.-ᵣ_) xs) = `-_` xs

  buildExpression t@(con (quote rat) _) = returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ [])
  buildExpression t@(con (quote lim) _) = returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ [])
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

      goal ← wrdℚ {A = Term} (inferType hole >>= normalise)

      wrdℚ {A = Term} (Wait.wait-for-type (debugPrint' "ratSolver" 20) goal)
      just (lhs , rhs) ← wrdℚ {A = Maybe (Term × Term)}
                (PathTypesReflection.get-boundary (debugPrint' "ratSolver" 20) goal)
        where
          nothing
            → typeError(strErr "The CommRingSolver failed to parse the goal "
                               ∷ termErr goal ∷ [])

      (lhs' , rhs' , vars) ← wrdℚ {A = Term × Term × Vars} (toAlgebraExpression (lhs , rhs))

      lhs*' ← wrdℚ  (unquoteTC {A = RExpr (length vars)} lhs')
      rhs*' ← wrdℚ  (unquoteTC {A = RExpr (length vars)} rhs')
      let lhs* = (normalize lhs*')
          rhs* = (normalize rhs*')
      wrdℚ $ debugPrint' "ratSolver" 20 (map,ₑ vars)
      (just ihr) ← pure (mkIHR {length vars} lhs* rhs*)
        where nothing → do
             lhs*tm ← wrdℚ (quoteTC lhs* >>= normalise)
             rhs*tm ← wrdℚ (quoteTC rhs* >>= normalise)
             typeError ("normalised, not equal! :" ∷nl lhs*tm ∷nl rhs*tm ∷ₑ [])

      let solution = solverCallAsTerm (variableList vars) lhs' rhs' ihr

      wrdℚ (unify hole solution)

macro
  ℝ! : Term → TC _
  ℝ! = solve!-macro false

  ℝ!dbg : Term → TC _
  ℝ!dbg = solve!-macro true
