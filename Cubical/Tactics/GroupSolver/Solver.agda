{-# OPTIONS --safe #-}

module Cubical.Tactics.GroupSolver.Solver where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.List as Li
open import Cubical.Data.Maybe as Mb

open import Cubical.Algebra.Group

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.GroupSolver.GroupExpression
open import Cubical.Tactics.GroupSolver.Reflection

private
  variable
    ℓ : Level

module _ (G : Group ℓ) where
 open GroupStr (snd G)
 data IsTrm : ⟨ G ⟩ → Type ℓ where
  is1g : IsTrm 1g
  isOp : ∀ x y → IsTrm (_·_ x y)
  isInv : ∀ x → IsTrm (inv x)


1g' : (G : Group ℓ) → ⟨ G ⟩
1g' G = GroupStr.1g (snd G)

module _ (skipInv : Bool) (tG : R.Term)  where
 tryG : ℕ → R.Term → R.TC (GE.GroupExpr R.Term)
 tryG' : Bool → ℕ →  R.Term → R.TC (GE.GroupExpr R.Term)

 try1g : R.Term → R.TC (GE.GroupExpr R.Term)
 try1g t = do
       _ ← R.unify t (R.def (quote 1g') [ varg tG ])
       R.returnTC GE.ε

 tryOp : ℕ → R.Term → R.TC (GE.GroupExpr R.Term)
 tryOp zero _ = R.typeError []
 tryOp (suc k) t = do
       tm ← (R.checkType (R.con (quote isOp)
          (varg R.unknown ∷ [ varg R.unknown ])) (R.def (quote IsTrm)
           ((varg tG) ∷ [ varg t ])))
       (t1 , t2) ← h tm
       t1' ← tryG' false k t1
       t2' ← tryG' false k t2
       R.returnTC (t1' GE.· t2')

  where

  h : R.Term → R.TC (R.Term × R.Term)
  h (R.con (quote isOp) l) = match2Vargs l
  h _ = R.typeError []

 tryInv : ℕ → R.Term → R.TC (GE.GroupExpr R.Term)
 tryInv zero _ = R.typeError []
 tryInv (suc k) t =  do
       tm ← -- R.noConstraints
        (R.checkType (R.con (quote isInv)
          ([ varg R.unknown ])) (R.def (quote IsTrm)
           ((varg tG) ∷ [ varg t ])))
       t1 ← h tm
       t1' ← tryG' true k t1
       R.returnTC (GE.inv t1')

  where
  h' : List (R.Arg R.Term) → R.TC (R.Term)
  h' (harg _ ∷ xs) = h' xs
  h' (varg t1 ∷ []) = R.returnTC t1
  h' _ = R.typeError []

  h : R.Term → R.TC (R.Term)
  h (R.con (quote isInv) l) = h' l
  h _ = R.typeError []


 atom : R.Term → R.TC (GE.GroupExpr R.Term)
 atom x = R.returnTC (GE.η x)


 tryG' _ zero _ = R.typeError [ (R.strErr "Magic number to low") ]
 tryG' b (suc k) t =
   R.catchTC
    (try1g t)
    (catchOrSkip (skipInv)(tryInv k t)
               (R.catchTC (tryOp k t)
                           (atom t)))

 tryG = tryG' false

groupSolverMain : Bool → R.Term → R.Term → R.Term → R.Term → R.TC Unit
groupSolverMain debugFlag skipInvsTM mbAtomsFromUserTM tG hole = do
 skipInvs ← R.unquoteTC skipInvsTM
 (_ , (t0 , t1)) ← inferEnds tG hole
 atomsFromUser ← quotedMaybe→maybeTerm mbAtomsFromUserTM
    >>= (Mb.rec (R.returnTC nothing) λ l → quotedList→ListOfTerms l >>= (R.returnTC ∘ just) )

 t0N ← R.normalise t0
 t1N ← R.normalise t1
 r0 ← tryG skipInvs tG 100 t0N
 r1 ← tryG skipInvs tG 100 t1N
 ul ← Mb.rec (uniqeAtoms (GE.atoms _ r0 ++ GE.atoms _ r1)) R.returnTC atomsFromUser
 (r0* , r0') ← travGroupExprTC (lookT ul) r0 >>= λ x → R.quoteTC x >>= λ x' → R.returnTC (x , x')
 (r1* , r1') ← travGroupExprTC (lookT ul) r1 >>= λ x → R.quoteTC x >>= λ x' → R.returnTC (x , x')

 final ← R.reduce (R.def (quote solve) (tG v∷ (quoteList ul) v∷ r0' v∷ r1' v∷ [] ))
 R.catchTC
  (R.unify hole final)
  (do finalTy ← R.inferType final
      (R.typeError
        (let finalInferedType =
                (R.strErr "finalTy: ") ∷ (R.termErr finalTy) ∷ [ R.strErr "\n" ]
             inferedEnds =
              ((R.strErr "LHS: ") ∷ (R.termErr t0N) ∷ (R.strErr "\n")
               ∷ (R.strErr "RHS: ") ∷  (R.termErr t1N)  ∷ [(R.strErr "\n")])
             groupExprEnds =
              ((R.strErr "LHS: ") ∷ (R.strErr (showNormalizedGEℕ r0*)) ∷ (R.strErr "\n")
               ∷ (R.strErr "RHS: ") ∷  (R.strErr (showNormalizedGEℕ r1*))  ∷ [(R.strErr "\n")])
             debugMsg = finalInferedType ++ inferedEnds ++ groupExprEnds ++ (Li.map R.termErr ul)
             failMsg = (R.strErr "LHS ≠ RHS ‼\n") ∷
                        groupExprEnds ++ R.strErr "\n" ∷ niceAtomList 0 ul
        in if debugFlag then debugMsg else failMsg )))

 where
 niceAtomList : ℕ → List (R.Term) → List R.ErrorPart
 niceAtomList _ [] = []
 niceAtomList k (x ∷ xs) =
   (R.strErr (mkNiceVar k  <> " = ") ∷ R.termErr x ∷ [ R.strErr "\n" ]) ++ niceAtomList (suc k) xs

macro
 solveGroupDebug : R.Term → R.Term → R.Term → R.Term → R.TC Unit
 solveGroupDebug = groupSolverMain false

 solveGroup : R.Term → R.Term → R.TC Unit
 solveGroup = groupSolverMain false (R.con (quote false) [])  (R.con (quote nothing) [])

 solveπ₁ : R.Term → R.Term → R.Term → R.TC Unit
 solveπ₁ atomExprList = groupSolverMain false (R.con (quote true) [])
   (R.con (quote just) ((harg {q = R.quantity-0} R.unknown) ∷ (harg {q = R.quantity-0} R.unknown)
     ∷ [ varg atomExprList ]))
