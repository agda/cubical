module Cubical.Tactics.CommRingSolverFast.RationalsReflection where

open import Cubical.Foundations.Prelude hiding (Type)

open import Agda.Builtin.Reflection as R hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)
import Cubical.Data.Nat as ℕ
open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Int.Fast.Base hiding (abs; _-_)
open import Cubical.Data.Int.Fast using (fromNegℤ; fromNatℤ)
open import Cubical.Data.Nat using (ℕ; discreteℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool
open import Cubical.Data.Bool.SwitchStatement
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_)
import Cubical.Data.Int.Fast as ℤ
open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing

open import Cubical.Tactics.CommRingSolverFast.AlgebraExpression
open import Cubical.Tactics.CommRingSolverFast.RawAlgebra
open import Cubical.Tactics.CommRingSolverFast.IntAsRawRing
open import Cubical.Tactics.CommRingSolverFast.Solver 

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Algebra.CommRing.Instances.Rationals.Fast
open import Cubical.Data.Rationals.Fast as ℚ
import Cubical.Data.NatPlusOne as NPO
import Cubical.HITs.SetQuotients as SetQuotient
import Cubical.Tactics.CommRingSolverFast.IntPlusReflection as IPR

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

  eqSpecsCallAsTerm : ℕ → Term → Term → Term
  eqSpecsCallAsTerm n lhs rhs =
    def
       (quote eqSpecs)
       (natAsTerm (just n) v∷ lhs v∷ rhs  v∷ [])

  -- eqSpecsCallWithVars : ℕ → Term → Term → Term → Term → Term
  -- eqSpecsCallWithVars n R homR lhs rhs =
  --     eqSpecsCallAsTerm R homR lhs rhs
  --     where
  --       variableList : Vars → Arg Term
  --       variableList [] = varg (con (quote emptyVec) [])
  --       variableList (t ∷ ts)
  --         = varg (con (quote _∷vec_) (t v∷ (variableList ts) ∷ []))


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

  buildExpression v@(var _ _) =
    returnTC ((λ ass → polynomialVariable (ass v)) , v ∷ [])
             
  buildExpression t@(con (quote SetQuotient.[_]) _) =
        returnTC ((λ _ → con (quote K) (t v∷ [])) , [])
    -- returnTC ((λ _ → con (quote K) ({!K!} v∷ [])) , [])

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

  toAlgebraExpressionLHS : Term → TC (Term × Vars)
  toAlgebraExpressionLHS lhs = do
      (e , vars) ← buildExpression lhs

      returnTC (
        let ass : VarAss
            ass n = indexOf n vars
        in (e ass , vars ))


private
  checkIsRing : Term → TC Term
  checkIsRing ring = checkType ring (def (quote CommRing) (unknown v∷ []))

  -- checkIsRingHom : Term → TC Term
  -- checkIsRingHom ring = checkType ring (def (quote CommRing) (unknown v∷ []))

  pickHelper : ℕ → TC (Name × Name)
  pickHelper ℕ.zero = typeError (strErr "pickHelper 0 - todo" ∷ [])
  pickHelper (ℕ.suc ℕ.zero) = returnTC (quote eqElim , quote eqElimTy)
  pickHelper (ℕ.suc (ℕ.suc ℕ.zero)) = returnTC (quote eqElim₂ , quote eqElim₂Ty)
  pickHelper (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero))) = returnTC (quote eqElim₃ , quote eqElim₃Ty)
  pickHelper (ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero)))) = returnTC (quote eqElim₄ , quote eqElim₄Ty)
  pickHelper (ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero))))) = returnTC (quote eqElim₅ , quote eqElim₅Ty)
  pickHelper (ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero)))))) =
   returnTC (quote eqElim₆ , quote eqElim₆Ty)
  pickHelper x = typeError (strErr "pickHelper - todo :" ∷ strErr (primShowNat x) ∷ [])


  extractNMs : Term → TC Term
  extractNMs (def (quote PathP) (_ h∷ _ v∷
       (con (quote SetQuotient.[_])
        (_ ∷ _ ∷ _ ∷ _ ∷ lhs v∷ [])) v∷
       (con (quote SetQuotient.[_])
        (_ ∷ _ ∷ _ ∷ _ ∷ rhs v∷ [])) v∷ [])) =
    returnTC (def (quote ℚ._∼_) (lhs v∷ rhs v∷ [])) 
  extractNMs t = typeError (strErr "failToMatch in extractNMs :\n" ∷ termErr t ∷ [])

  wrdℕ : ∀ {a} {A : Type a} → TC A → TC A
  wrdℕ = withReduceDefs
     (false , ((quote ℕ._·_) ∷
        (quote ℕ._+_) ∷ (quote ℤ._+_) ∷ (quote (ℤ.-_)) ∷ (quote ℤ._·_) ∷ (quote _ℕ-_) ∷ []))

  stripLam : Term → TC Term
  stripLam (lam v (abs ai (lam v' (abs ai' x)))) = do
    s ← extendContext "z" (harg {q = quantity-ω} (def (quote ℤ) []))
        (extendContext "n" (harg {q = quantity-ω} (def (quote ℕ) []))
          (stripLam x))
    returnTC ((lam v (R.abs ai (lam v' (R.abs ai' s)))))
  stripLam x = do
   ty ← wrdℕ (inferType x >>= normalise)
   ty2 ← wrdℕ (extractNMs ty >>= normalise)

   h2 ← wrdℕ (checkType unknown ty2)
   -- wrdℕ (debugPrint "ratSolverVars" 20 (termErr ty ∷ []))
   IPR.solve!-macro h2
   wrdℕ $ checkType (def (quote ℚ.eqℚ) (h2 v∷ [])) ty
   
  wrdℚ : ∀ {a} {A : Type a} → TC A → TC A
  wrdℚ = withReduceDefs
     (false , ((quote ℚ._+_) ∷ (quote (ℚ.-_)) ∷ (quote ℚ._·_)
       -- ∷ []))
      ∷ (quote NPO._+₁_) ∷ (quote NPO._·₊₁_) ∷ (quote NPO.ℕ₊₁→ℕ) ∷ (quote ℚ.ℕ₊₁→ℤ) ∷ []))

  
  solve!-macro : Term → TC Unit
  solve!-macro hole = 
    do
      commRing ← wrdℚ $ checkIsRing (def (quote ℚCommRing) [])
      
      goal ← wrdℚ $ inferType hole >>= normalise
      names ← wrdℚ $ findRingNames commRing

      wrdℚ $ wait-for-type goal
      just (lhs , rhs) ← wrdℚ $ get-boundary goal
        where
          nothing
            → typeError(strErr "The RationalReflecion CommRingSolver failed to parse the goal "
                               ∷ termErr goal ∷ [])

      (lhs' , rhs' , vars) ← wrdℚ $ CommRingReflection.toAlgebraExpression commRing names (lhs , rhs)
      printVars "ratSolverVars" vars
      -- typeError (strErr "solve!-macro" ∷ [])
      (hnm , tynm) ← pickHelper (length vars)
      let eqSpecsTm = eqSpecsCallAsTerm (length vars) lhs' rhs'
      -- ty ← R.inferType eqSpecsTm >>= R.normalise
      sharedHole ← wrdℚ $ checkType unknown (def tynm (eqSpecsTm v∷ []))
      let solveℚTm = def hnm ((eqSpecsTm v∷ sharedHole v∷ []) ++ map varg vars)
      tm' ← wrdℚ $ checkType solveℚTm goal
      ss ← stripLam sharedHole
      unify ss sharedHole
      unify hole solveℚTm
      -- typeError (termErr sharedHole ∷ [])


macro
  ℚ! : Term → TC _
  ℚ! = solve!-macro
