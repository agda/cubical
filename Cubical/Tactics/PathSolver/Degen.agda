{-# OPTIONS --safe #-}
module Cubical.Tactics.PathSolver.Degen where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Interpolate

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma


import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base renaming (v to 𝒗)
open import Cubical.Reflection.Sugar

open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.QuoteCubical
open import Cubical.Tactics.Reflection.CuTerm
open import Cubical.Tactics.Reflection.Error


undegenTerm : Bool → ℕ → ℕ → R.Term → R.TC R.Term
undegenTerm onEnd offset dim =
    atVarOrDefM.rv
      (λ n k _ args → R.var (n + k) <$> args)
      h
      zero ∘S (if onEnd then (idfun _) else (liftVarsFrom 1 (offset + dim)))

 where

  g :  R.Name → List (R.Arg R.Term) → R.Term → Maybe R.Term
  g (quote _∨_) a@(_ v∷ v[ _ ]) tm = just tm
  g (quote _∧_) a@(_ v∷ v[ _ ]) tm = just tm
  g (quote ~_) a@(v[ _ ]) tm = just tm
  g _ _ _ = nothing

  h : ℕ →
        R.Name →
        List (R.Arg R.Term) → R.TC (List (R.Arg R.Term)) → R.TC R.Term
  h _ nm arg argM =
     Mb.rec (R.def nm <$> argM)
            ((extractIExprM >=&
              (IExpr→Term
              ∘ mapVarsInIExpr (_+ offset)
              ∘ undegen onEnd dim
              ∘ mapVarsInIExpr (_∸ offset) )))
       (g nm arg (R.def nm arg))

undegenTerm2 : Bool → ℕ → ℕ → R.Term → R.TC R.Term
undegenTerm2 onEnd offset dim =
    atVarOrDefM.rv
      (λ n k _ args → R.var (n + k) <$> args)
      h
      zero ∘S (if onEnd then (idfun _) else (liftVarsFrom 1 (offset + dim)))

 where

  g :  R.Name → List (R.Arg R.Term) → R.Term → Maybe R.Term
  g (quote _∨_) a@(_ v∷ v[ _ ]) tm = just tm
  g (quote _∧_) a@(_ v∷ v[ _ ]) tm = just tm
  g (quote ~_) a@(v[ _ ]) tm = just tm
  g _ _ _ = nothing

  h : ℕ →
        R.Name →
        List (R.Arg R.Term) → R.TC (List (R.Arg R.Term)) → R.TC R.Term
  h _ nm arg argM =
     Mb.rec (R.def nm <$> argM)
            ((extractIExprM >=&
              (IExpr→Term
              ∘ mapVarsInIExpr (_+ offset)
              ∘ undegen2 onEnd dim
              ∘ mapVarsInIExpr (_∸ offset) )))
       (g nm arg (R.def nm arg))



private
  variable
    ℓ : Level
    A : Type ℓ
    CongGuard : Type


module UndegenCell (dim : ℕ) where

 undegenCell : (R.Term × R.Term) → R.Term → R.TC R.Term
 undegenCell (t0 , tI) t = do
   let eai = (extractAllIExprs t0)
   -- concatMapM (pure ∘S ("" ∷nl_) ∘S [_]ₑ ∘S IExpr→Term) eai >>= R.typeError

   fe ← undegenFcs dim eai --(extractAllIExprs t0)

   -- Mb.rec (pure t)
   let ie = IExpr→Term (F→I dim fe)
   pure
   -- addNDimsToCtx (suc dim) $ R.typeError $ [_]ₑ $
     (R.def (quote hcomp)
          (vlam "undegenCellDim"
            (R.def (quote primPOr)
              (R.def (quote ~_) v[ 𝒗 (suc dim) ] v∷ (R.def (quote _∨_) ((𝒗 (suc dim)) v∷
                v[ (liftVars ie) ])) v∷
               (constPartialR (R.def (quote ~_) v[ 𝒗 (suc dim) ]) (liftVarsFrom 1 (suc dim) tI))
                 v∷ v[ constPartialR ((R.def (quote _∨_) ((𝒗 (suc dim)) v∷
                v[ (liftVars ie) ]))) (liftVars t) ])) v∷ v[ t ]))
   where
    constPartialR : R.Term → R.Term → R.Term
    constPartialR tI tA = R.def (quote constPartial) (tA v∷ v[ tI ])


 mbUndegen : R.Term → R.TC (Maybe (R.Term × R.Term) × R.Term)
 mbUndegen tm = do

  allNonDeg ← foldrM
            (\ie b →  (b and_)  <$> (isNonDegen dim ie))
              true (extractAllIExprs tm)
  if allNonDeg then (pure (nothing , tm)) else
    do idt0 ← undegenTerm2 true zero dim tm
       idt1 ← undegenTerm2 false zero dim tm
       pure ( just (tm , idt1) , idt0)

 mbUndegen' : R.Term → R.TC (Maybe (R.Term × R.Term) × R.Term)
 mbUndegen' tm = do

  allNonDeg ← foldrM
            (\ie b →  (b and_)  <$> (isNonDegen dim ie))
              true (extractAllIExprs tm)
  if allNonDeg then (pure (nothing , tm)) else
    do idt0 ← undegenTerm true zero dim tm
       idt1 ← undegenTerm false zero dim tm
       pure ( just (tm , idt1) , idt0)

