module Cubical.Tactics.CommRingSolver.Specialised.Rationals where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Reflection.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Bool
import Cubical.Data.FinData as FD
import Cubical.Data.Vec as V
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Maybe
open import Cubical.Data.List
open import Cubical.Data.Fast.Int using (_ℕ-_)
import Cubical.Data.Fast.Int as ℤ
import Cubical.Data.Fast.Int.Order as ℤ

import Cubical.HITs.SetQuotients as SetQuotient

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)

open import Cubical.Reflection.Sugar

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Error

open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order
open import Cubical.Algebra.CommRing.Instances.Rationals

open import Cubical.Tactics.CommRingSolver.Config
open import Cubical.Tactics.CommRingSolver.Solver
open import Cubical.Tactics.CommRingSolver.AlgebraExpression
open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Tactics.CommRingSolver.GenericCommRing

open import Cubical.Data.NatPlusOne
import Cubical.HITs.SetQuotients as SetQuotient

open import Cubical.Tactics.CommRingSolver.Specialised.FastIntPlus

open EqElims

_ : Q[ ℕ.suc 3 ℕ.+ 12 ]≡ lit (nat 16)
_ = showQuotedN [] ((ℕ.suc 3) ℕ.+ 12)

_ : Q[ ℤ.pos (ℕ.suc 3 ℕ.+ 12) ℤ.- 40 ]≡
     con (quote ℤ.negsuc) v[ lit (nat 23) ]
_ = showQuotedN [] (ℤ.pos ((ℕ.suc 3) ℕ.+ 12) ℤ.- 40)


_ : Q[ 1+ (ℕ.suc 3 ℕ.+ 12) ]≡ con (quote 1+_) v[ lit (nat 16) ]
_ = showQuotedN [] (1+ ((ℕ.suc 3) ℕ.+ 12))


-- someℚ : ℚ
-- someℚ = [ -3 / 12 ]

-- someℚ' : ℚ
-- someℚ' = 1 + 0


-- _ : {!!}
-- _ = showQuotedN someℚ'


mbConcreteℚ' : Term → TC (Maybe Term)
mbConcreteℚ' tm@(con (quote SetQuotient.[_])
     (_ ∷ _ ∷ _ ∷ _ ∷
      v[ con (quote _,_) (_ ∷ _ ∷ _ ∷ _ ∷ con _ v[ lit _ ] v∷ v[ con (quote 1+_) v[ lit _ ] ]) ])) =
       pure (just tm)
mbConcreteℚ' tm  = pure nothing




mbConcreteℚ : Term → TC (Maybe Term)
mbConcreteℚ tm =
 withNormalisation true
  (withReconstructed true
   (withReduceDefs (false , []) (checkType tm q[ ℚ ]  >>= mbConcreteℚ')))



macro
 wrTest : Term → Term → TC Unit
 wrTest x _ =
   withReduceDefs (false , quote ℕ._+_ ∷ quote ℕ._·_ ∷ [])
    (withReduceDefs (false , [])
    (normalise x >>= typeError ∘ [_]ₑ))


-- _ : _
-- _ = wrTest (1+ ((ℕ.suc 3) ℕ.+ 12))

ℚmatcher : RingReflectionMatcher
ℚmatcher .RingReflectionMatcher.mkMatchTermTC _ _ =  pure matchTerm

   where

   module _ (be : (Term → TC (Template × Vars))) where
    open BE q[ ℚCommRing ] be

    matchTerm : Term → TC (Maybe (Template × Vars))
    matchTerm t@(def (quote -_) xs) = just <$> `-_` xs
    matchTerm t@(def (quote _+_) xs) = just <$> `_+_` xs
    matchTerm t@(def (quote _·_) xs) = just <$> `_·_` xs
    matchTerm t = map-Maybe (λ t' → (λ _ → con (quote K) v[ t' ]) , []) <$> mbConcreteℚ t


open Discrete ℚCommRing discreteℚ ℚCommRingIsNotZeroRing
              nothing nothing nothing

              (quoteDefsfNames ( _·_ ω∷ _+_ ω∷ (-_) ω∷ ω[] ))
              ℚmatcher
               renaming (solve! to ℚ!!) public


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
       ((quoteTC ℚ₊ >>= checkType (var v [])) >> pure (just (v , [ℚ₊])))
   <|> ((quoteTC ℚ >>= checkType (var v [])) >> pure (just (v , [ℚ])))
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



wrdℕ : ∀ {a} {A : Type a} → TC A → TC A
wrdℕ = withReduceDefs
   (false , ((quote ℕ._·_) ∷
    (quote ℕ._+_) ∷ (quote ℤ._+_) ∷ (quote (ℤ.-_)) ∷ (quote ℤ._·_) ∷ (quote _ℕ-_)
     -- ∷ []))
     ∷ (quote _+₁_) ∷ (quote _·₊₁_) ∷ (quote ℕ₊₁→ℕ) ∷ (quote ℤ.ℕ₊₁→ℤ)
      ∷ (quote ℤ.0<→ℕ₊₁-fst) ∷ []))


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
  wrdℚ = withReduceDefs ( false , ((quoteDefsfNames
      (ℚ._+_ ω∷ ℚ.-_ ω∷ _·_ ω∷ ℕ._·_ ω∷ ℕ._+_ ω∷ ℤ._+_ ω∷ (ℤ.-_)
      ω∷ ℤ._·_ ω∷ _ℕ-_ ω∷ _+₁_ ω∷ _·₊₁_ ω∷ ℕ₊₁→ℕ ω∷ ℤ.ℕ₊₁→ℤ
       ω∷ ℤ.0<→ℕ₊₁-fst ω∷ ω[])) ++ doNotUnfoldsℚ))



  solve!!-macro : Term → TC Unit
  solve!!-macro hole =
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
      when dbg
        (typeError [ sigTm ]ₑ)
      lemType ← wrdℚ $  normalise (def (quote LemType) (sigTm v∷ lrhs v∷ []))
      wrdℚ $ debugPrint' "ratSolver" 20 ("ℚLemType: " ∷nl [ lemType ]ₑ)
      when dbg do eqType ← wrdℚ $  normalise (def (quote LemType) (sigTm v∷ lrhs v∷ []))
                  wrdℚ $ debugPrint' "ratSolver" 20 ("ℚEqType: " ∷nl [ eqType ]ₑ)
      -- lemType ← wrdℚ $  normalise (def (quote LemType) (sigTm v∷ lrhs v∷ []))
      -- sharedHole ← wrdℚ $ checkType unknown lemType

      sbi ← atTargetLam lemType λ tgTy → do
        tgTy2 ← wrdℕ $ normalise tgTy >>= extractNMs
        debugPrint' "ratSolver" 20 [ tgTy2 ]ₑ
        wrdℚ $ debugPrint' "ratSolver" 20 ("ℤLemType: " ∷nl [ tgTy2 ]ₑ)
        h2 ← checkType unknown tgTy2
        -- FastℤPlusRingSolver.solve!-macro h2 -- IPR.solve!-macro h2
        FastℤPlusRingSolver.solve!-macro h2
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
  ℚ! = solve!!-macro false

  ℚ!dbg : Term → TC _
  ℚ!dbg = solve!!-macro true


-- -- private
-- --  module _ (zring : CommRing ℓ-zero) where
-- --   module ETNF = EqualityToNormalform ℚCommRing ℚCommRing
-- --                  (idCommRingHom _)
-- --   module ETNF≟ = ETNF.Decidable discreteℚ (λ _ → nothing) nothing nothing nothing
-- --           (just ℚ'.ℚCommRingIsNotZeroRing) (just (λ _ x → x))
-- -- macro
-- --   ℚ! : Term → TC _
-- --   ℚ! = CommRingSolver.solve!-macro ℚCommRing ℚCommRing nothing ℚMatcher
-- --       ((quote ℕ._·_) ∷ (quote ℕ._+_) ∷ (quote _+_) ∷ (quote (-_)) ∷ (quote _·_) ∷ [])
-- --       (quote ETNF.solveByDec) (quote ETNF≟.HF-Maybe-prf)
-- --       λ _ → pure true



-- module ℚ!!-tests where

--  test1 : 1 + 0 ≡ 1
--  test1  = ℚ!!
