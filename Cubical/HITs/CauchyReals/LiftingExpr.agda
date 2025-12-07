module Cubical.HITs.CauchyReals.LiftingExpr where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty
open import Cubical.Data.Unit

open import Cubical.Data.Rationals.Fast as ℚ using (ℚ ; [_/_])
open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness



open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function
open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)
open import Cubical.Reflection.Sugar

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat.Literals
open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Error

record _isLiftOf_ (fℝ : ℝ → ℝ) (fℚ : ℚ → ℚ) : Type where
 constructor inj
 field
  prf : ∀ q → rat (fℚ q) ≡ fℝ (rat q)
  
record LiftedTo (fℝ : ℝ → ℝ) : Type where 
 constructor inj
 field
  fℚ : _
  prf : fℝ isLiftOf fℚ
  
 open _isLiftOf_ prf
 
record LiftedFrom (fℚ : ℚ → ℚ) : Type where 
 constructor inj
 field
  fℝ : _
  prf : fℝ isLiftOf fℚ
  
 open _isLiftOf_ prf

record _isLiftOf₂_ (fℝ : ℝ → ℝ → ℝ) (fℚ : ℚ → ℚ → ℚ) : Type where
 constructor inj
 field
  prf : ∀ q q' → rat (fℚ q q') ≡ fℝ (rat q) (rat q')



record LiftedTo₂ (fℝ : ℝ → ℝ → ℝ) : Type where 
 constructor inj
 field
  fℚ : _
  prf : fℝ isLiftOf₂ fℚ

 open _isLiftOf₂_ prf
 
record LiftedFrom₂ (fℚ : ℚ → ℚ → ℚ) : Type where 
 constructor inj
 field
  fℝ : _
  prf : fℝ isLiftOf₂ fℚ

 open _isLiftOf₂_ prf

instance
 liftedTo : ∀ {fℝ fℚ} → ⦃ fℝ isLiftOf fℚ ⦄ → LiftedTo fℝ
 liftedTo ⦃ lo ⦄ .LiftedTo.fℚ = _
 liftedTo ⦃ lo ⦄ .LiftedTo.prf = lo

 liftedFrom : ∀ {fℝ fℚ} → ⦃ fℝ isLiftOf fℚ ⦄ → LiftedFrom fℚ
 liftedFrom .LiftedFrom.fℝ = _
 liftedFrom ⦃ lo ⦄ .LiftedFrom.prf = lo


 liftedTo₂ : ∀ {fℝ fℚ} → ⦃ fℝ isLiftOf₂ fℚ ⦄ → LiftedTo₂ fℝ
 liftedTo₂ ⦃ lo ⦄ .LiftedTo₂.fℚ = _
 liftedTo₂ ⦃ lo ⦄ .LiftedTo₂.prf = lo

 liftedFrom₂ : ∀ {fℝ fℚ} → ⦃ fℝ isLiftOf₂ fℚ ⦄ → LiftedFrom₂ fℚ
 liftedFrom₂ .LiftedFrom₂.fℝ = _
 liftedFrom₂ ⦃ lo ⦄ .LiftedFrom₂.prf = lo


data ℚExpr : Type where
 𝕢[_] : ℚ → ℚExpr 
 _$𝕢[_] : ∀ fℚ → ⦃ lf : LiftedFrom fℚ ⦄ → ℚExpr → ℚExpr
 _$𝕢₂[_,_] : ∀ fℚ → ⦃ lf : LiftedFrom₂ fℚ ⦄ → ℚExpr → ℚExpr → ℚExpr

evalℚExpr : ℚExpr → ℚ
evalℚExpr (𝕢[ x ]) = x
evalℚExpr (fℚ $𝕢[ x ]) = fℚ (evalℚExpr x)
evalℚExpr (fℚ $𝕢₂[ x , x₁ ]) = fℚ (evalℚExpr x) (evalℚExpr x₁)

module ℝExpr (ratFlag : Type) where 
 data ℝExpr : Type where
  ratE : {ratFlag} → ℚExpr →  ℝExpr 
  𝕣[_] : ℝ → ℝExpr
  _$𝕣[_] : ∀ fℝ → ⦃ lt : LiftedTo fℝ ⦄ → ℝExpr → ℝExpr
  _$𝕣₂[_,_] : ∀ fℝ → ⦃ lt : LiftedTo₂ fℝ ⦄ → ℝExpr → ℝExpr → ℝExpr
  rat-path : ∀ q {rf} → ratE {rf} 𝕢[ q ] ≡ 𝕣[ rat q ]
  lift-path : ∀ {fℝ fℚ rf} ⦃ lo : fℝ isLiftOf fℚ ⦄ {q} →
                   ratE {rf} (_$𝕢[_] fℚ ⦃ inj fℝ lo ⦄ q) ≡
                     _$𝕣[_] fℝ ⦃ inj fℚ lo ⦄ (ratE {rf} q)
  lift-path₂ : ∀ {fℝ fℚ rf} ⦃ lo : fℝ isLiftOf₂ fℚ ⦄ {q q'} →
                   ratE {rf} (_$𝕢₂[_,_] fℚ ⦃ inj fℝ lo ⦄ q q') ≡
                     _$𝕣₂[_,_] fℝ ⦃ inj fℚ lo ⦄ (ratE {rf} q) (ratE {rf} q')
  isSetℝExpr : isSet ℝExpr


open ℝExpr hiding (ℝExpr) public

ℚℝExpr = ℝExpr.ℝExpr Unit
ℝExpr = ℝExpr.ℝExpr ⊥

ℚExpr→ℝExpr : ℚExpr → ℝExpr
ℚExpr→ℝExpr 𝕢[ x ] = 𝕣[ rat x ]
ℚExpr→ℝExpr (_$𝕢[_] fℚ ⦃ inj fℝ prf ⦄ x) = _$𝕣[_] fℝ ⦃ inj _ prf ⦄ (ℚExpr→ℝExpr x)
ℚExpr→ℝExpr (_$𝕢₂[_,_] fℚ ⦃ inj fℝ prf ⦄ x x₁) = 
 _$𝕣₂[_,_] fℝ ⦃ inj _ prf ⦄ (ℚExpr→ℝExpr x) (ℚExpr→ℝExpr x₁)

ℚℝExpr→ℝExpr : ℚℝExpr → ℝExpr
ℚℝExpr→ℝExpr (ratE x) = ℚExpr→ℝExpr x
ℚℝExpr→ℝExpr 𝕣[ x ] = 𝕣[ x ]
ℚℝExpr→ℝExpr (_$𝕣[_] fℝ ⦃ lt ⦄ x) =
  (_$𝕣[_] fℝ ⦃ lt ⦄ (ℚℝExpr→ℝExpr x))
ℚℝExpr→ℝExpr (_$𝕣₂[_,_] fℝ {{lo}} x x₁) =
  (_$𝕣₂[_,_] fℝ {{lo}} (ℚℝExpr→ℝExpr x) (ℚℝExpr→ℝExpr x₁))

ℚℝExpr→ℝExpr (rat-path q i) = 𝕣[ rat q ]
ℚℝExpr→ℝExpr (lift-path {fℝ} {fℚ} ⦃ lo = inj prf ⦄ {q} i) =
 _$𝕣[_] fℝ ⦃ inj fℚ (inj prf) ⦄ (ℚExpr→ℝExpr q)
ℚℝExpr→ℝExpr (lift-path₂ {fℝ} {fℚ} ⦃ lo = lo ⦄ {q} {q'} i) =
 _$𝕣₂[_,_] fℝ ⦃ inj fℚ lo ⦄ (ℚExpr→ℝExpr q)
         (ℚExpr→ℝExpr q')
ℚℝExpr→ℝExpr (isSetℝExpr x x₁ x₂ y i i₁) =
  isSetℝExpr (ℚℝExpr→ℝExpr x) (ℚℝExpr→ℝExpr x₁)
   (cong ℚℝExpr→ℝExpr x₂) (cong ℚℝExpr→ℝExpr y) i i₁

evalℚℝExpr : ∀ {ratFlag} → ℝExpr.ℝExpr ratFlag → ℝ
evalℚℝExpr (ratE x) = rat (evalℚExpr x)
evalℚℝExpr 𝕣[ x ] = x
evalℚℝExpr (fℝ $𝕣[ x ]) = fℝ (evalℚℝExpr x)
evalℚℝExpr (fℝ $𝕣₂[ x , x₁ ]) = fℝ (evalℚℝExpr x) (evalℚℝExpr x₁)
evalℚℝExpr (rat-path q i) = rat q
evalℚℝExpr (lift-path ⦃ lo = lo ⦄ {q} i) = _isLiftOf_.prf lo (evalℚExpr q) i 
evalℚℝExpr (lift-path₂ ⦃ lo = lo ⦄ {q} {q'} i) =
  _isLiftOf₂_.prf lo (evalℚExpr q) (evalℚExpr q') i
evalℚℝExpr (isSetℝExpr x x₁ x₂ y i i₁) =
 isSetℝ (evalℚℝExpr x) (evalℚℝExpr x₁)
  (cong evalℚℝExpr x₂) (cong evalℚℝExpr y) i i₁

evalCohRat : ∀ e → rat (evalℚExpr e) ≡ evalℚℝExpr (ℚExpr→ℝExpr e)
evalCohRat 𝕢[ x ] = refl
evalCohRat (_$𝕢[_] fℚ ⦃ inj fℝ (inj prf) ⦄ e) = 
   prf (evalℚExpr e) 
   ∙ cong fℝ (evalCohRat e)
evalCohRat (_$𝕢₂[_,_] fℚ ⦃ inj fℝ (inj prf) ⦄ e e₁) =
  prf (evalℚExpr e) (evalℚExpr e₁)  
   ∙ cong₂ fℝ (evalCohRat e) (evalCohRat e₁)

evalCoh : ∀ e → evalℚℝExpr e ≡ evalℚℝExpr (ℚℝExpr→ℝExpr e)
evalCoh (ratE x) = evalCohRat x
evalCoh 𝕣[ x ] = refl
evalCoh (fℝ $𝕣[ e ]) = cong fℝ (evalCoh e)
evalCoh (fℝ $𝕣₂[ e , e₁ ]) = cong₂ fℝ (evalCoh e) (evalCoh e₁)
evalCoh (rat-path q i) j = rat q
evalCoh (lift-path {fℝ} {fℚ} ⦃ lo = inj prf ⦄ {q} i) j =
  isSet→isSet' isSetℝ
    (prf (evalℚExpr q) ∙ cong fℝ (evalCohRat q))
    (λ j → fℝ (evalCohRat q j))
    (prf (evalℚExpr q))
    refl
    i j 

evalCoh (lift-path₂ {fℝ} {fℚ} ⦃ lo = inj prf ⦄ {q} {q'} i) j =
   isSet→isSet' isSetℝ
   (prf (evalℚExpr q) (evalℚExpr q') ∙
      λ i₁ → fℝ (evalCohRat q i₁) (evalCohRat q' i₁) )
   (λ j → fℝ (evalCohRat q j) (evalCohRat q' j))
   (prf (evalℚExpr q) (evalℚExpr q'))
   refl
   i j 

evalCoh (isSetℝExpr e e₁ x y i i₁) j =
  isGroupoid→isGroupoid' (isSet→isGroupoid isSetℝ)
    (cong evalCoh x)
    (cong evalCoh y)
    (λ _ → evalCoh e)
    (λ _ → evalCoh e₁)
    (isSetℝ (evalℚℝExpr e) (evalℚℝExpr e₁)
         (λ i₂ → evalℚℝExpr (x i₂)) (λ i₂ → evalℚℝExpr (y i₂)))
    (isSetℝ (evalℚℝExpr (ℚℝExpr→ℝExpr e))
         (evalℚℝExpr (ℚℝExpr→ℝExpr e₁))
         (λ i₂ → evalℚℝExpr (ℚℝExpr→ℝExpr (x i₂)))
         (λ i₂ → evalℚℝExpr (ℚℝExpr→ℝExpr (y i₂))))
    i i₁ j

evalCoh' : ∀ e → evalℚℝExpr (ℚℝExpr→ℝExpr e) ≡ evalℚℝExpr e
evalCoh' e = sym (evalCoh e)

private

 ifHasInstanceℚ₂ : Name → TC Bool
 ifHasInstanceℚ₂ nm = runSpeculative $ (_, false) <$> (do
  (meta m _) ← checkType
     unknown (def (quote _isLiftOf₂_) (unknown v∷ v[ (def nm []) ]))
   where _ → typeError [ "imposible in liftingExpr macro!" ]ₑ  
  [] ← getInstances m
   where (x ∷ _) → pure true
   -- ((solveInstanceConstraints >> pure true) <|> pure false)
      
  pure false)
  
 toExprℚ : Term → TC Term
 toExprℚ (def nm v[ q ]) = do
   e ← toExprℚ q
   pure (con (quote _$𝕢[_]) ((def nm []) v∷ v[ e ]))
 toExprℚ tm@(def nm (q v∷ v[ q' ])) = do
   e ← toExprℚ q
   e' ← toExprℚ q'
   b ← ifHasInstanceℚ₂ nm
   if b
    then (pure (con (quote _$𝕢₂[_,_]) ((def nm []) v∷ e v∷ v[ e' ])))
    else (pure (con (quote 𝕢[_]) (v[ tm ])))
 toExprℚ tm = pure (con (quote 𝕢[_]) (v[ tm ]))
 
-- _$𝕣[_] fℝ ⦃ inj fℚ (inj prf) ⦄ (ℚExpr→ℝExpr q)
 toExprℝ : Term → TC Term
 toExprℝ (def nm v[ r ]) = do
   e ← toExprℝ r
   pure (con (quote _$𝕣[_]) ((def nm []) v∷ v[ e ]))
 toExprℝ (def nm (r v∷ v[ r' ])) = do
   e ← toExprℝ r
   e' ← toExprℝ r'
   pure (con (quote _$𝕣₂[_,_]) ((def nm []) v∷ e v∷ v[ e' ]))
 toExprℝ (con (quote rat) (v[ q ])) =
   do
   e ← toExprℚ q
   pure (con (quote ratE) (v[ e ]))
 toExprℝ tm = pure (con (quote 𝕣[_]) (v[ tm ]))
 
 quoteℚℝ : Term → TC Term
 quoteℚℝ tm' = do
  tm ← checkType tm' (def (quote ℝ) [])
  toExprℝ tm


 wrdℚ : ∀ {a} {A : Type a} → TC A → TC A
 wrdℚ = withReduceDefs
    (false , ((quote ℚ.max) ∷ (quote (ℚ.min)) ∷ (quote ℚ.abs') ∷
              (quote ℚ._+_) ∷ (quote (ℚ.-_)) ∷ (quote ℚ._·_) ∷ []))

 ℚℝ!-macro : Term → TC Unit
 ℚℝ!-macro hole = wrdℚ $
   do
     goal ← inferType hole >>= normalise
    

     wait-for-type goal
     just (lhs , rhs) ← get-boundary goal
       where
         nothing
           → typeError(strErr "The ℚℝ failed to parse the goal "
                              ∷ termErr goal ∷ [])
     lhsE ← quoteℚℝ lhs
     rhsE ← quoteℚℝ rhs
     -- typeError [ rhsE ]ₑ
     let solution =
           def (quote _∙_)
            (def (quote evalCoh) v[ lhsE ] v∷ v[
             def (quote evalCoh') v[ rhsE ] ])   
     unify hole solution

 ℚℝ!↘-macro : Term → TC Unit
 ℚℝ!↘-macro hole = wrdℚ $
   do
     goal ← inferType hole >>= normalise
    

     wait-for-type goal
     just lhs ← get-boundaryLHS goal
       where
         nothing
           → typeError(strErr "The ℚℝ↘ failed to parse the goal "
                              ∷ termErr goal ∷ [])
     lhsE ← quoteℚℝ lhs
     let solution = def (quote evalCoh) v[ lhsE ]   
     unify hole solution


macro
 quoteℚℝ! : Term → Term →  TC Unit
 quoteℚℝ! tm hole = quoteℚℝ tm >>= unify hole

 ℚℝ! : Term →  TC Unit
 ℚℝ! = ℚℝ!-macro

 ℚℝ!↘ : Term →  TC Unit
 ℚℝ!↘ = ℚℝ!↘-macro
