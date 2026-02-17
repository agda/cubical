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

open import Cubical.Data.Int using (fromNegℤ; fromNatℤ)
open import Cubical.Data.Nat using (ℕ; discreteℕ) renaming (_+_ to _+ℕ_)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Bool
open import Cubical.Data.Bool.SwitchStatement
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_)

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing

open import Cubical.Tactics.CommRingSolver.AlgebraExpression
open import Cubical.Tactics.CommRingSolver.RawAlgebra
open import Cubical.Tactics.CommRingSolver.Solver
open import Cubical.Tactics.CommRingSolver.GenericCommRing
open import Cubical.Reflection.Sugar
open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Utilities

import Cubical.Data.Fast.Int as Fastℤ
import Cubical.Algebra.CommRing.Instances.Fast.Int as Fastℤ'

import Cubical.Data.Rationals as ℚ
import Cubical.Algebra.CommRing.Instances.Rationals as ℚ'
import Cubical.HITs.SetQuotients as SetQuotient

private
 variable
  ℓ' ℓ : Level




module CommRingSolver
         (ring : CommRing ℓ)
         (rrm : RingReflectionMatcher)
         (doNotUnfold : List Name)
         (solverName : Name)
         (solverPrfName : Name)
                      where

 module CommRingReflection  where

  open RingReflectionMatcher rrm

  Fuel = ℕ

  fuelBudget : Fuel
  fuelBudget = 10000000

  module _ (cring : Term) where
   module _ (matchTerm : (Term → TC (Template × Vars)) → Term → TC (Maybe (Template × Vars))) where
    open pr

    buildExpression : Fuel → Term → TC (Template × Vars)
    buildExpression (ℕ.zero) t =
      typeError ("OutOfFuel in Cubical.Tactics.CommRingSolver.GenericCommRing" ∷nl [ t ]ₑ)

    buildExpression (ℕ.suc 𝓕) t = do
      (just x) ← matchTerm  (buildExpression 𝓕) t
        where nothing → returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ [])
      returnTC x

   toAlgebraExpression : Term × Term → TC (Term × Term × Vars)
   toAlgebraExpression (lhs , rhs) = do

       matchTerm ← mkMatchTermTC cring
       r1 ← buildExpression matchTerm fuelBudget lhs
       r2 ← buildExpression matchTerm fuelBudget rhs
       vars ← returnTC (appendWithoutRepetition (snd r1) (snd r2))
       returnTC (
         let ass : VarAss
             ass n = indexOf n vars
         in (fst r1 ass , fst r2 ass , vars ))




 solverCallWithVars : ℕ → Vars → Term → Term → Term → Term
 solverCallWithVars n vars R lhs rhs =
     def solverName --(quote ?)
         (R v∷ (harg {quantity-ω} (ℕAsTerm n)) ∷ lhs v∷ rhs
           v∷ (variableList vars)
           ∷ (def solverPrfName  (R v∷ (harg {quantity-ω} (ℕAsTerm (length vars))) ∷ v[ lhs ]))
            v∷ [])

     where
       variableList : Vars → Arg Term
       variableList [] = varg (con (quote emptyVec) [])
       variableList (t ∷ ts)
         = varg (con (quote _∷vec_) (t v∷ (variableList ts) ∷ []))


 solve!-macro : Term → TC Unit
 solve!-macro hole = withReduceDefs
     (false , doNotUnfold)
   do
     commRing ← quoteTC ring
     goal ← inferType hole >>= normalise


     wait-for-type goal
     just (lhs , rhs) ← get-boundary goal
       where
         nothing
           → typeError(strErr "The CommRingSolver failed to parse the goal "
                              ∷ termErr goal ∷ [])

     (lhs' , rhs' , vars) ← CommRingReflection.toAlgebraExpression commRing (lhs , rhs)
     -- typeError (map,ₑ vars ++ₑ map,ₑ (lhs ∷ rhs ∷ []))

     let solution = solverCallWithVars (length vars) vars commRing lhs' rhs'
     unify hole solution <|> do
       solutionType ←
              (inferType solution >>= normalise)
                 <|> typeError (map,ₑ vars ++ₑ map,ₑ (lhs ∷ rhs ∷ []))
       typeError (("solution type: " ∷nl [ solutionType ]ₑ) ++nl (map,ₑ vars ++nl map,ₑ (lhs' ∷ rhs' ∷ [])))

module _ (ring : CommRing ℓ) where

 private
  module ETNF =  EqualityToNormalform Fastℤ'.ℤCommRing Fastℤ.discreteℤ ring
                  (_ , Fastℤ'.CanonicalHomFromℤ.isHomFromℤ ring)

 macro
   solve! : Term → TC _
   solve! = CommRingSolver.solve!-macro ring
    (GenericCommRingReflection.genericCommRingMatchTerm) [] (quote ETNF.solve) (quote ETNF.HF-refl)


module FastℤRingSolver where
 open Fastℤ hiding (_+'_)
 open Fastℤ'

 fastℤMatcher : RingReflectionMatcher
 fastℤMatcher .RingReflectionMatcher.mkMatchTermTC _ = returnTC matchTerm

  where

  scalarℕ : ℕ → TC (Template × Vars)
  scalarℕ n = returnTC (((λ _ →
    con (quote K) (con (quote pos) (lit (nat n) v∷ []) v∷ [])) , []))

  module _ (be : (Term → TC (Template × Vars))) where
   open BE be



   buildExpressionFromNat : Term → TC (Template × Vars)
   buildExpressionFromNat (lit (nat x)) = scalarℕ x
   buildExpressionFromNat (con (quote ℕ.zero) []) = `0` []
   buildExpressionFromNat (con (quote ℕ.suc) (con (quote ℕ.zero) [] v∷ [] )) = `1` []
   buildExpressionFromNat (con (quote ℕ.suc) (x v∷ [] )) =
     do
     -- debugPrint "intSolver" 20  (strErr "fromNat suc:" ∷ termErr x ∷ [])
     r1 ← `1` []
     r2 ← buildExpressionFromNat x
     returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
              appendWithoutRepetition (snd r1) (snd r2))
   buildExpressionFromNat (def (quote ℕ._+_) (x v∷ y v∷ [])) =
     do
     -- debugPrint "intSolver" 20  (strErr "buildNateExpr ℕ._+_ :" ∷ termErr x ∷ [])
     r1 ← buildExpressionFromNat x
     r2 ← buildExpressionFromNat y
     returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
              appendWithoutRepetition (snd r1) (snd r2))
   buildExpressionFromNat (def (quote ℕ._·_) (x v∷ y v∷ [])) =
     do
     r1 ← buildExpressionFromNat x
     r2 ← buildExpressionFromNat y
     returnTC ((λ ass → con (quote _·'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
              appendWithoutRepetition (snd r1) (snd r2))
   buildExpressionFromNat (def (quote _ℕ-_) (x v∷ (con (quote ℕ.suc) (y v∷ [] )) v∷ [])) =
     do
     r1 ← buildExpressionFromNat x
     r2 ← do y' ← do u1 ← `1` []
                     u2 ← buildExpressionFromNat y
                     returnTC {A = Template × Vars} ((λ ass → con (quote _+'_) (fst u1 ass v∷ fst u2 ass v∷ [])) ,
                          appendWithoutRepetition (snd u1) (snd u2))
             returnTC {A = Template × Vars} ((λ ass → con (quote -'_) (fst y' ass v∷ [])) , snd y')
     returnTC ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
              appendWithoutRepetition (snd r1) (snd r2))
   buildExpressionFromNat t' =
    let t = (con (quote ℤ.pos) (t' v∷ []))
    in (returnTC ((λ ass → polynomialVariable (ass t)) , t ∷ []))



   matchTerm : Term → TC (Maybe (Template × Vars))

   matchTerm t@(con (quote ℤ.pos) (x v∷ [])) = do
    -- debugPrint "intSolver" 20  (strErr "buildExpr pos:" ∷ termErr x ∷ [])
    just <$> buildExpressionFromNat x
   matchTerm t@(con (quote ℤ.negsuc) (x v∷ [])) =
    do --debugPrint "intSolver" 20  (strErr "buildExpr negsuc:" ∷ termErr x ∷ [])
       y ← do r1 ← `1` []
              r2 ← buildExpressionFromNat x
              returnTC {A = Template × Vars} ((λ ass → con (quote _+'_) (fst r1 ass v∷ fst r2 ass v∷ [])) ,
                   appendWithoutRepetition (snd r1) (snd r2))
       just <$> returnTC ((λ ass → con (quote -'_) (fst y ass v∷ [])) , snd y)

   matchTerm t@(def (quote -_) xs) = just <$> `-_` xs
   matchTerm t@(def (quote _+_) xs) = just <$> `_+_` xs
   matchTerm t@(def (quote _·_) xs) = just <$> `_·_` xs

   matchTerm _ = returnTC nothing

 private
  module _ (zring : CommRing ℓ-zero) where
   module ETNF = EqualityToNormalform ℤCommRing discreteℤ ℤCommRing
                  (idCommRingHom _)

 macro
   ℤ! : Term → TC _
   ℤ! = CommRingSolver.solve!-macro ℤCommRing fastℤMatcher
       ((quote ℕ._·_) ∷ (quote ℕ._+_) ∷ (quote _+_) ∷ (quote (-_)) ∷ (quote _·_) ∷ (quote _ℕ-_) ∷ [])
       (quote ETNF.solve) (quote ETNF.HF-refl)

module ℚRingSolver where
 open ℚ
 open ℚ'

 ℚMatcher : RingReflectionMatcher
 ℚMatcher .RingReflectionMatcher.mkMatchTermTC _ = returnTC matchTerm

  where

  module _ (be : (Term → TC (Template × Vars))) where
   open BE be

   matchTerm : Term → TC (Maybe (Template × Vars))

   matchTerm t@(con (quote SetQuotient.[_]) _) =
      returnTC (just ((λ _ → con (quote K) v[ t ]) , []))

   matchTerm t@(def (quote -_) xs) = just <$> `-_` xs
   matchTerm t@(def (quote _+_) xs) = just <$> `_+_` xs
   matchTerm t@(def (quote _·_) xs) = just <$> `_·_` xs

   matchTerm _ = returnTC nothing

 private
  module _ (zring : CommRing ℓ-zero) where
   module ETNF = EqualityToNormalform ℚCommRing discreteℚ ℚCommRing
                  (idCommRingHom _)

 macro
   ℚ! : Term → TC _
   ℚ! = CommRingSolver.solve!-macro ℚCommRing ℚMatcher
       ((quote ℕ._·_) ∷ (quote ℕ._+_) ∷ (quote _+_) ∷ (quote (-_)) ∷ (quote _·_) ∷ [])
       (quote ETNF.solveByDec) (quote ETNF.HF-unit)
