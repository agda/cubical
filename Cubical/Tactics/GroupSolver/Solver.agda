{-# OPTIONS --safe #-}

module Cubical.Tactics.GroupSolver.Solver where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

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

module tryGE (skipInv : Bool) (tG : R.Term)  where
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
 (_ , (t0 , t1)) ← inferEnds hole
 atomsFromUser ← quotedMaybe→maybeTerm mbAtomsFromUserTM
    >>= (Mb.rec (R.returnTC nothing) λ l → quotedList→ListOfTerms l >>= (R.returnTC ∘ just) )

 t0N ← R.normalise t0
 t1N ← R.normalise t1
 r0 ← tryGE.tryG skipInvs tG 100 t0N
 r1 ← tryGE.tryG skipInvs tG 100 t1N
 ul ← Mb.rec (uniqeAtoms (GE.atoms _ r0 ++ GE.atoms _ r1)) R.returnTC atomsFromUser
 (r0* , r0') ← travGroupExprTC (lookT ul) r0 >>= λ x → R.quoteTC x >>= λ x' → R.returnTC (x , x')
 (r1* , r1') ← travGroupExprTC (lookT ul) r1 >>= λ x → R.quoteTC x >>= λ x' → R.returnTC (x , x')

 final ← R.reduce (R.def (quote Solver.solve) (tG v∷ (quoteList ul) v∷ r0' v∷ r1' v∷ [] ))
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
 solveGroupDebug = groupSolverMain true

 solveGroup : R.Term → R.Term → R.TC Unit
 solveGroup = groupSolverMain false (R.con (quote false) [])  (R.con (quote nothing) [])

 -- solveπ₁ : R.Term → R.Term → R.Term → R.TC Unit
 -- solveπ₁ atomExprList = groupSolverMain false (R.con (quote true) [])
 --   (R.con (quote just) ((harg {q = R.quantity-0} R.unknown) ∷ (harg {q = R.quantity-0} R.unknown)
 --     ∷ [ varg atomExprList ]))


module _ (A : Type ℓ) (a : A)  where

 data IsΩTrm : a ≡ a → Type ℓ where
  isRefl : IsΩTrm refl
  isComp : (x y z : _) → IsΩTrm (x ∙∙ y ∙∙ z)

 module _ (p q r : a ≡ a) where
  zz : IsΩTrm (p ∙∙ q ∙∙ r)
  zz = isComp _ _ _

module tryΩE (qt-A qt-a : R.Term)  where

 tryΩ : ℕ → R.Term → R.TC (GE.π₁GroupExpr R.Term)


 tryRefl : R.Term → R.TC (GE.π₁GroupExpr R.Term)
 tryRefl t = do
       -- R.debugPrint "" 1 $ R.strErr "tryRefl\n" ∷  [ R.termErr t ]
       _ ← R.checkType
             (R.con (quote isRefl) [])
             (R.def (quote IsΩTrm) (qt-A v∷ qt-a v∷ [ varg t ]))
       R.returnTC GE.reflGE

 tryComp : ℕ → R.Term → R.TC (GE.π₁GroupExpr R.Term)
 tryComp zero _ = R.typeError []
 tryComp (suc k) t = do
       -- R.debugPrint "" 1 $ R.strErr "tryComp\n" ∷  [ R.termErr t ]
       tm ← R.checkType
             (R.con (quote isComp) (R.unknown v∷ R.unknown v∷ [ varg R.unknown ]))
             (R.def (quote IsΩTrm) (qt-A v∷ qt-a v∷ [ varg t ]))
       (t1 , t2 , t3) ← h tm
       -- R.debugPrint "" 1 $ R.strErr "sucess Comp!\n"
       --                      ∷ R.termErr t1 ∷ R.strErr "\n"
       --                      ∷ R.termErr t2 ∷ R.strErr "\n"
       --                      ∷ R.termErr t3 ∷ R.strErr "\n"
       --                      ∷ []
       t1' ← tryΩ k t1
       t2' ← tryΩ k t2
       t3' ← tryΩ k t3
       R.returnTC (t1' GE.·· t2' ·· t3')

  where

  h : R.Term → R.TC (R.Term × R.Term × R.Term)
  h (R.con (quote isComp) l) = match3Vargs l
  h _ = R.typeError []


 atom : R.Term → R.TC (GE.π₁GroupExpr R.Term)
 atom x = R.returnTC (GE.atomGE x)


 tryΩ zero _ = R.typeError [ (R.strErr "Magic number to low") ]
 tryΩ (suc k) t =
   R.catchTC
    (tryRefl t)
    (R.catchTC (tryComp k t) (atom t))

-- appI : {A : Type ℓ} {a : A} → Path A a a → I → A
-- appI p i = p i

unLam : R.Term → R.TC R.Term
unLam (R.lam _ (R.abs _ t)) = R.returnTC t
unLam t = R.typeError []

appendIfUniqe : R.Term → List R.Term →   R.TC (List R.Term)
appendIfUniqe x [] = R.returnTC [ x ]
appendIfUniqe x xs@(x₁ ∷ xs') = do
 x' ← R.checkType x (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>= unLam
 x₁' ← R.checkType x₁ (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>= unLam
 sym[x₁'] ← R.checkType (R.def (quote sym) [ varg x₁ ]) (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>= unLam
 R.catchTC (R.extendContext "i" (varg (R.def (quote I) [])) $
                ( R.noConstraints $ R.unify (x') (x₁') >> R.returnTC xs))
    (
      R.catchTC
     (R.extendContext "i" (varg (R.def (quote I) [])) $
                ( R.noConstraints $ R.unify (x') sym[x₁'] >> R.returnTC xs))
        (appendIfUniqe x xs' >>= (R.returnTC ∘ (x₁ ∷_))  )
        )

comparePathTerms : R.Term → R.Term → R.TC (Maybe Bool)
comparePathTerms x x₁ = do
 x' ← R.checkType x (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>= unLam
 x₁' ← R.checkType x₁ (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>= unLam
 sym[x₁'] ← R.checkType (R.def (quote sym) [ varg x₁ ]) (R.def (quote _≡_) (R.unknown v∷ R.unknown v∷ [])) >>= unLam
 R.catchTC (R.extendContext "i" (varg (R.def (quote I) [])) $
                ( R.noConstraints $ R.unify (x') (x₁') >> R.returnTC (just true)))
    (
      R.catchTC
     (R.extendContext "i" (varg (R.def (quote I) [])) $
                ( R.noConstraints $ R.unify (x') sym[x₁'] >> R.returnTC (just false)))
        (R.returnTC nothing)
        )

concatUniq : List R.Term → List R.Term →  R.TC (List R.Term)
concatUniq [] = R.returnTC
concatUniq (x ∷ x₂) x₁  = appendIfUniqe x x₁ >>= concatUniq x₂

indexOfAlways : R.Term → List R.Term →   R.TC ((List R.Term) × (Bool × ℕ))
indexOfAlways t [] = R.returnTC ([ t ] , (true , 0))
indexOfAlways t xs@(x ∷ xs') =
  comparePathTerms t x >>=
   Mb.rec ((λ (l , (b , k) ) → (x ∷ l) , (b , (suc k))) <$> indexOfAlways t xs' )
          (λ b → R.returnTC (xs , (b , 0)))

gatherUniqeAtomPaths : GE.π₁GroupExpr R.Term → R.TC (List R.Term)
gatherUniqeAtomPaths = flip w []
 where

 w : GE.π₁GroupExpr R.Term → List R.Term →  R.TC (List R.Term)
 w (GE.atomGE x) l = appendIfUniqe x l
 w GE.reflGE l = R.returnTC l
 w (x GE.·· x₁ ·· x₂) l = do l' ← w x l ; w x₁ l' >>= w x₂


unMapAtoms : List R.Term → GE.π₁GroupExpr R.Term →
     (R.TC ((List R.Term) × GE.π₁GroupExpr (Bool × ℕ)))
unMapAtoms l (GE.atomGE x) =
 do (l' , y) ← indexOfAlways x l
    R.returnTC (l' , GE.atomGE y)
unMapAtoms l GE.reflGE = R.returnTC (l , GE.reflGE)
unMapAtoms l (e GE.·· e₁ ·· e₂) = do
  (l' , e') ← unMapAtoms l e
  (l'' , e₁') ← unMapAtoms l' e₁
  (l''' , e₂') ← unMapAtoms l'' e₂
  (R.returnTC (l''' , (e' GE.·· e₁' ·· e₂')))



π₁groupSolverMain : Bool → R.Term → R.Term → R.Term → R.Term → R.TC Unit
π₁groupSolverMain debugFlag t-A t-isGrpA t-a hole = do
 (_ , (t0 , t1)) ← inferEnds hole
 t0N ← R.normalise t0
 t1N ← R.normalise t1
 r0 ← tryΩE.tryΩ t-A t-a 100 t0N
 r1 ← tryΩE.tryΩ t-A t-a 100 t1N
 (aL' , e0) ← unMapAtoms [] r0
 (aL , e1) ← unMapAtoms aL' r1
 e0Q ← R.quoteTC e0
 e1Q ← R.quoteTC e1

 let dbgInfo =   (R.strErr "LHS: ") ∷ (R.strErr $ showπ₁GEℕ e0)
               ∷ (R.strErr "\n")
               ∷ (R.strErr "RHS: ") ∷  (R.strErr $ showπ₁GEℕ e1)
               ∷ (R.strErr "\n")
               ∷ ((niceAtomList 0 aL))

 final ← R.reduce (R.def (quote πSolver.solveπ) (t-A v∷ t-isGrpA v∷ t-a v∷ (quoteList aL)
    v∷ e0Q v∷ e1Q v∷ [] ))
 R.catchTC
  (R.unify hole final)
  (R.typeError $ (R.strErr "LHS ≢ RHS \n\n") ∷ dbgInfo)

 where
 niceAtomList : ℕ → List (R.Term) → List R.ErrorPart
 niceAtomList _ [] = []
 niceAtomList k (x ∷ xs) =
   (R.strErr (mkNiceVar k  <> " = ") ∷ R.termErr x ∷ [ R.strErr "\n" ]) ++ niceAtomList (suc k) xs

macro
 π₁solveGroupDebug : R.Term → R.Term → R.Term → R.Term → R.TC Unit
 π₁solveGroupDebug = π₁groupSolverMain true

 π₁solveGroup : R.Term → R.Term → R.Term → R.Term → R.TC Unit
 π₁solveGroup = π₁groupSolverMain false
