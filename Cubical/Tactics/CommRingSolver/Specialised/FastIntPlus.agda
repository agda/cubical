module Cubical.Tactics.CommRingSolver.Specialised.FastIntPlus where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat.Literals

open import Cubical.Data.Int as Slowℤ using (fromNegℤ; fromNatℤ)
open import Cubical.Data.Nat using (ℕ; discreteℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatPlusOne
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Bool
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_)

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing

import Cubical.Algebra.CommRing.Properties as CommRingProperties
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Tactics.CommRingSolver.AlgebraExpression

open import Cubical.Tactics.CommRingSolver.Solver
open import Cubical.Tactics.CommRingSolver.Config
open import Cubical.Tactics.CommRingSolver.GenericCommRing
open import Cubical.Reflection.Sugar
open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Utilities using (quoteDefsfNames;ω[];_ω∷_) public
open import Cubical.Tactics.Reflection.Goals

open import Cubical.Data.Int using (ℤ;pos;negsuc)
open import Cubical.Data.Fast.Int as Fastℤ hiding (_+'_)
import Cubical.Data.Fast.Int.Order as ℤ
import Cubical.Algebra.CommRing.Instances.Fast.Int as Fastℤ'

-- import Cubical.Data.Rationals as ℚ
-- import Cubical.Algebra.CommRing.Instances.Rationals as ℚ'
import Cubical.HITs.SetQuotients as SetQuotient

open import Cubical.Data.List.Dependent as DL using (_∷_ ; P[_] ; []) public
import Cubical.Algebra.AbGroup.Base as AbGroup

open import Cubical.Tactics.CommRingSolver.Config
open import Cubical.Tactics.CommRingSolver.Reflection

-- module _ (k : ℕ₊₁) where
--  _ : Q[ pos (Fastℤ.abs (ℕ₊₁→ℤ k)) ]≡
--       con (quote pos)
--       v[ def (quote Fastℤ.abs) v[ def (quote ℕ₊₁→ℤ) v[ var 0 [] ] ] ]
--  _ = showQuotedN
--       (quoteDefsfNames (ℕ₊₁→ℤ ω∷ sign  ω∷ ω[]))
--        (pos (Fastℤ.abs (ℕ₊₁→ℤ k)))


module FastℤPlusRingSolver where
 open Fastℤ hiding (_+'_)
 open Fastℤ'

 FastℤPlusMatcher : RingReflectionMatcher
 FastℤPlusMatcher .RingReflectionMatcher.mkMatchTermTC _ _ = returnTC matchTerm

  where

  scalarℕ : ℕ → TC (Template × Vars)
  scalarℕ n = returnTC (((λ _ →
    con (quote K) (con (quote ℤ.pos) (lit (nat n) v∷ []) v∷ [])) , []))

  module _ (be : (Term → TC (Template × Vars))) where
   open BE q[ ℤCommRing ] be

   Fuel = ℕ

   buildExpression : Fuel → Term → TC (Template × Vars)

   natPlusVariable : Term → TC (Template × Vars)
   natPlusVariable t' =
    let t = (con (quote ℤ.pos) (con (quote ℕ.suc) ((def (quote ℕ₊₁.n) (t' v∷ [])) v∷ []) v∷ []))
    in (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))

   buildExpressionFromNat : Fuel → Term → TC (Template × Vars)
   buildExpressionFromNatPlus : Fuel → Term → TC (Template × Vars)
   buildExpressionFromNatPlus  ℕ.zero _ = typeError [ strErr "outOfFuel" ]
   buildExpressionFromNatPlus f (def (quote _·₊₁_) (x v∷ y v∷ [])) =
    do debugPrint "intSolverVars" 20  (strErr "fromNatPlus t3:" ∷nl x ∷nl y ∷ₑ [])
       r1 ← buildExpressionFromNatPlus f x
       r2 ← buildExpressionFromNatPlus f y
       returnTC ((λ ass → con (quote _·'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
                appendWithoutRepetition (snd r1) (snd r2))



   buildExpressionFromNatPlus f (x@(var _ [])) = natPlusVariable x

   buildExpressionFromNatPlus f t@(con (quote 1+_) (x@(var _ []) v∷ [])) =
     natPlusVariable t


   buildExpressionFromNatPlus f (con (quote 1+_) ((con (quote ℕ.zero) []) v∷ [])) =
     scalarℕ 1 -- `1` []
   buildExpressionFromNatPlus (ℕ.suc f) (con (quote 1+_) ((con (quote ℕ.suc) (x v∷ [])) v∷ [])) =
    do r1 ← scalarℕ 1 -- `1` []
       r2 ← buildExpressionFromNatPlus f (con (quote 1+_) (x v∷ []))
       returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
                appendWithoutRepetition (snd r1) (snd r2))

   buildExpressionFromNatPlus f (con (quote 1+_) ((lit (nat x)) v∷ [])) = scalarℕ (ℕ.suc x)

   buildExpressionFromNatPlus f (con (quote 1+_) ((def (quote ℕ₊₁.n) (x v∷ []) ) v∷ [])) =
    do  debugPrint "intSolverVars" 20  (strErr "fromNatPlus t1:" ∷ termErr x ∷ [])
        buildExpressionFromNatPlus f x

   buildExpressionFromNatPlus (ℕ.suc f) (def (quote ℤ.0<→ℕ₊₁-fst) (x v∷ [])) =
      buildExpression f x
   buildExpressionFromNatPlus (ℕ.suc f) (con (quote 1+_)
      ((def (quote ℕ._+_) (n v∷
       (def (quote ℕ._·_) (m v∷ sn v∷ [])) v∷ [])) v∷ [])) = do
     unify (con (quote ℕ.suc) (n v∷ [] )) sn
     debugPrint "intSolverVars" 20  (strErr "fromNatPlus t2:" ∷nl termErr n ∷nl termErr m ∷  [])

     buildExpressionFromNatPlus f (def (quote _·₊₁_)
      (con (quote 1+_) (m v∷ []) v∷
       con (quote 1+_) (n v∷ []) v∷
       []))


   buildExpressionFromNatPlus f t' = natPlusVariable t'


   buildExpressionFromNat f t@(lit (nat x)) = -- typeError (strErr "scalar: " ∷ termErr t ∷ [])
     scalarℕ x --buildExpressionFromNatLit x
   buildExpressionFromNat f (con (quote ℕ.zero) []) = scalarℕ 0 -- `0` []
   buildExpressionFromNat f (con (quote ℕ.suc) (con (quote ℕ.zero) [] v∷ [] )) = scalarℕ 1 -- `1` []
   buildExpressionFromNat f (con (quote ℕ.suc) ((def (quote ℕ₊₁.n) (n v∷ [])) v∷ [] ))
    = buildExpressionFromNatPlus f n
   buildExpressionFromNat f (con (quote ℕ.suc) (x v∷ [] )) =
     do
     debugPrint "intSolver" 20  (strErr "fromNat suc:" ∷ termErr x ∷ [])
     r1 ← scalarℕ 1 -- `1` []
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
     r2 ← do y' ← do u1 ← scalarℕ 1 -- `1` []
                     u2 ← buildExpressionFromNat f y
                     returnTC {A = Template × Vars} ((λ ass → con (quote _+'_) (fst u1 ass v∷ fst u2 ass v∷ [])) ,
                          appendWithoutRepetition (snd u1) (snd u2))
             returnTC {A = Template × Vars} ((λ ass → con (quote -'_) (fst y' ass v∷ [])) , snd y')
     returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
              appendWithoutRepetition (snd r1) (snd r2))
   buildExpressionFromNat (ℕ.suc f) (def (quote Fastℤ.abs) v[ t@(def (quote ℕ₊₁→ℤ) _) ]) =
    buildExpression f t
   buildExpressionFromNat (ℕ.suc f) (def (quote ℕ₊₁→ℕ) (x v∷ [])) =
    buildExpressionFromNatPlus f x
   buildExpressionFromNat f t' =
    let t = (con (quote ℤ.pos) (t' v∷ []))
    in returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ [])


   buildExpression ℕ.zero _ = typeError [ strErr "outOfFuel" ]
   buildExpression f (def (quote ℕ₊₁→ℤ) (x v∷ [])) =
    buildExpressionFromNatPlus f x

   buildExpression f t@(var _ _) =
     returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ [])



   buildExpression f (def (quote _+_) xs) = `_+_` xs
   buildExpression f (def (quote _·_) xs) = `_·_` xs
   buildExpression f (def (quote -_) xs) = `-_` xs
   buildExpression f (def (quote sign) v[ def (quote ℕ₊₁→ℤ) v[ _ ] ] ) = scalarℕ 1
   buildExpression f t@(def _ xs) =
        (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))

   buildExpression f t@(con (quote pos) (x v∷ [])) = do
     debugPrint "intSolver" 20  (strErr "buildExpr pos:" ∷ termErr x ∷ [])
     buildExpressionFromNat f x
   buildExpression f t@(con (quote negsuc) ((def (quote ℕ₊₁.n) (x v∷ []) ) v∷ [])) =
     do y ← buildExpressionFromNatPlus f x
        returnTC ((λ ass → con (quote -'_) (fst y ass v∷ [])) , snd y)
   buildExpression f t@(con (quote negsuc) (x v∷ [])) =
    do debugPrint "intSolver" 20  (strErr "buildExpr negsuc:" ∷ termErr x ∷ [])
       y ← do r1 ← scalarℕ 1 -- `1` []
              r2 ← buildExpressionFromNat f x
              returnTC {A = Template × Vars} ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
                    appendWithoutRepetition (snd r1) (snd r2))
       returnTC ((λ ass → con (quote -'_) (fst y ass v∷ [])) , snd y)

   buildExpression f t = errorOut' t


   matchTerm : Term → TC (Maybe (Template × Vars))
   matchTerm tm = just <$> buildExpression 10000 tm



 config : CommRingSolverConfig
 config .CommRingSolverConfig.ℓ = _
 config .CommRingSolverConfig.ℓ` = _
 config .CommRingSolverConfig.R = Fastℤ'.ℤCommRing
 config .CommRingSolverConfig.commAlg =
  Fastℤ'.ℤCommRing , idCommRingHom _
 config .CommRingSolverConfig.mbDiscreteScalars = just Fastℤ.discreteℤ
 config .CommRingSolverConfig.mbNeg?Scalar = just mbNegℤ
 config .CommRingSolverConfig.mbCommonDenom = just cdℤ
 config .CommRingSolverConfig.mb·`lCancel = just ·lCancelℤ
 config .CommRingSolverConfig.mbNotZeroRing = just (Slowℤ.0≢1-ℤ ∘S sym)
 config .CommRingSolverConfig.mb≢0r→≢0r` = just λ _ z → z
 config .CommRingSolverConfig.ringReflectionMatcher = FastℤPlusMatcher
 config .CommRingSolverConfig.doNotUnfold =
  quoteDefsfNames (ℕ._·_ ω∷ ℕ._+_ ω∷ _+_ ω∷ (-_) ω∷ _·_ ω∷ _ℕ-_ ω∷ _+₁_ ω∷ _·₊₁_ ω∷ ℕ₊₁→ℕ ω∷ ℕ₊₁→ℤ
    ω∷ ℤ.0<→ℕ₊₁-fst ω∷ ω[])

 config .CommRingSolverConfig.polyVarGuard = (λ _ → pure true)
 config .CommRingSolverConfig.scalarSolver = (λ _ _ → pure false)

 open CommRingSolver config hiding (solve!-lemma-macro) public

open FastℤPlusRingSolver public using () renaming (solve! to ℤ+!)
