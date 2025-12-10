module Cubical.Tactics.CommRingSolverFast.RationalsReflection where

open import Cubical.Foundations.Prelude hiding (Type)

open import Agda.Builtin.Reflection as R hiding (Type)
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as ℕ
open import Cubical.Reflection.Base
open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Utilities

open import Cubical.Reflection.Sugar
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)
open import Agda.Builtin.String
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function

open import Cubical.Data.List

open import Cubical.Data.Bool
open import Cubical.Data.Int.Fast using (ℤ)
import Cubical.Data.Int.Fast as ℤ

open import Cubical.Tactics.Reflection
open import Cubical.Algebra.CommRing.Instances.Rationals.Fast
open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚ
import Cubical.Data.NatPlusOne as NPO
import Cubical.HITs.SetQuotients as SetQuotient
import Cubical.Tactics.CommRingSolverFast.IntPlusReflection as IPR

open ℚ.EqElims

abstractℚandℚ₊ : Term → TC (List (ℕ × ℚTypes) × Term)
abstractℚandℚ₊ tm = do

  fv ← (zipWithIndex ∘ catMaybes) <$> (mapM mbℚVar (freeVars tm))
  -- quoteTC fv >>= normalise >>= (typeError ∘ [_]ₑ)
  let N = length fv
  let tm' = remapVars (rmpV N fv) tm
  pure (rev (map snd fv) , absV fv tm')
 where
 mbℚVar : ℕ → TC (Maybe (ℕ × ℚTypes))
 mbℚVar v =
       ((quoteTC ℚ.ℚ₊ >>= checkType (var v [])) >> pure (just (v , [ℚ₊])))
   <|> ((quoteTC ℚ.ℚ >>= checkType (var v [])) >> pure (just (v , [ℚ])))
   <|> pure nothing

 rmpV : ℕ → (List (ℕ × ℕ × ℚTypes)) → ℕ → ℕ
 rmpV N [] k = N ℕ.+ k
 rmpV N ((i , j , qTy) ∷ xs) k =
  if k =ℕ j then i else rmpV N xs k

 vNm : ℚTypes → String
 vNm [ℚ] = "q"
 vNm [ℚ₊] = "₊q"

 absV : (List (ℕ × ℕ × ℚTypes)) → Term → Term
 absV [] tm = tm
 absV (x ∷ xs) tm = absV xs (vlam (vNm (snd (snd x))) tm)



_,ℚ_ : ℚ → ℚ → ℚ × ℚ
_,ℚ_ = _,_

doNotUnfoldsℚ : List Name
doNotUnfoldsℚ = quote ℚ.abs ∷ quote ℚ.max ∷ quote ℚ.min ∷ []


module _ (dbg : Bool) where


  debugPrint' : String → ℕ → List ErrorPart → TC Unit
  debugPrint' = if dbg then debugPrint else (λ _ _ _ → pure _)


  extractNMs : Term → TC Term
  extractNMs (def (quote PathP) (_ h∷ _ v∷
       (con (quote SetQuotient.[_])
        (_ ∷ _ ∷ _ ∷ _ ∷ lhs v∷ [])) v∷
       (con (quote SetQuotient.[_])
        (_ ∷ _ ∷ _ ∷ _ ∷ rhs v∷ [])) v∷ [])) =
    returnTC (def (quote ℚ._∼_) (lhs v∷ rhs v∷ []))
  extractNMs t = typeError (strErr "failToMatch in extractNMs :\n" ∷ termErr t ∷ [])


  wrdℚ : ∀ {a} {A : Type a} → TC A → TC A
  wrdℚ = withReduceDefs
     (false , ((quote ℚ._+_) ∷ (quote (ℚ.-_)) ∷ (quote ℚ._·_)
       -- ∷ []))
      ∷ (quote NPO._+₁_) ∷ (quote NPO._·₊₁_) ∷ (quote NPO.ℕ₊₁→ℕ) ∷ (quote ℚ.ℕ₊₁→ℤ) ∷ doNotUnfoldsℚ))


  solve!-macro : Term → TC Unit
  solve!-macro hole =
    do


      goal ← wrdℚ $ inferType hole >>= normalise


      wrdℚ $ Wait.wait-for-type (debugPrint' "ratSolver" 20) goal
      just (lhs , rhs) ← wrdℚ $ PathTypesReflection.get-boundary (debugPrint' "ratSolver" 20) goal
        where
          nothing
            → typeError(strErr "The RationalReflecion CommRingSolver failed to parse the goal "
                               ∷ termErr goal ∷ [])
      let lrhs₀ = def (quote _,ℚ_) (lhs v∷ v[ rhs ])

      (sigℚ , lrhs) ← abstractℚandℚ₊ lrhs₀
      wrdℚ $ debugPrint' "ratSolver" 20 [ lrhs ]ₑ

      sigTm ← quoteTC (map snd sigℚ)
      lemType ← wrdℚ $  normalise (def (quote LemType) (sigTm v∷ lrhs v∷ []))
      wrdℚ $ debugPrint' "ratSolver" 20 ("ℚLemType: " ∷nl [ lemType ]ₑ)
      when dbg do eqType ← wrdℚ $  normalise (def (quote LemType) (sigTm v∷ lrhs v∷ []))
                  wrdℚ $ debugPrint' "ratSolver" 20 ("ℚEqType: " ∷nl [ eqType ]ₑ)
      -- lemType ← wrdℚ $  normalise (def (quote LemType) (sigTm v∷ lrhs v∷ []))
      -- sharedHole ← wrdℚ $ checkType unknown lemType

      sbi ← atTargetLam lemType λ tgTy → do
        tgTy2 ← IPR.wrdℕ $ normalise tgTy >>= extractNMs
        debugPrint' "ratSolver" 20 [ tgTy2 ]ₑ
        wrdℚ $ debugPrint' "ratSolver" 20 ("ℤLemType: " ∷nl [ tgTy2 ]ₑ)
        h2 ← checkType unknown tgTy2
        IPR.solve!-macro h2
        debugPrint' "ratSolver" 20 [ "ints solved!" ]ₑ
        pure (def (quote ℚ.eqℚ) (h2 v∷ []))

      let solveℚTm = def (quote EllimEqₛ) ((sigTm v∷ lrhs v∷ v[ sbi ]) ++
               map (λ (i , _) → varg (var i []))  sigℚ)
      debugPrint' "ratSolver" 20 [ "pre unify checkpoint" ]ₑ
      unify hole solveℚTm
      -- -- typeError [] --(termErr sharedHole ∷ [])
-- atTargetLam

macro
  ℚ! : Term → TC _
  ℚ! = solve!-macro false

  ℚ!dbg : Term → TC _
  ℚ!dbg = solve!-macro true
