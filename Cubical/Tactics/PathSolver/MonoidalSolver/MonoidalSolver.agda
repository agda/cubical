{-

This module implements a solver capable of handling squares, which are boundaries built of one-dimensional faces. At this stage, it does not support higher-dimensional cubes.

**Simplified One-Dimensional View**:
  - Represents compositions involving only one interval variable.
  - Defined using the specialized `1DimView` type.
  - Equipped with instances of both `RawMonad` and `RawApplicative`.
  - Simplifies the manipulation and normalization of paths within the solver
    (compared to more general, arbitrary dimensional CuTerm representation)

### Solver steps:

1. **Identifying Boundaries**:
   - The solver begins by identifying the boundary of a square term.

2. **Quoting into Specialized Representation**:
   - The boundary terms are quoted into a specialized one-dimensional representation using the `quote1D` function.

3. **Applying Generalized `cong-∙`**:
   - (if necessary) Uses the  `fillCongs` functions from the `CongComp` module to "push to the bottom" all application of functions (bring all the composiitons to the "top")

4. **Filler Construction**:
   - Constructs fillers for each face using the `_↙_` operator from the `PathEval` module.
   - Relies on the aspects of the free monoidal groupoid structure as implemented in `PathEval`.

5. **Assembling the Final Square**:
   - The final square term is assembled using the `◪mkSq` lemma from `Path.agda`.

-}

{-# OPTIONS --safe #-}
module Cubical.Tactics.PathSolver.MonoidalSolver.MonoidalSolver where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat


open import Cubical.Data.Sigma

open import Cubical.Reflection.Base renaming (v to 𝒗)
open import Cubical.Reflection.Sugar
import Agda.Builtin.Reflection as R

open import Cubical.Tactics.Reflection

open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Variables

open import Cubical.Tactics.PathSolver.CongComp

open import Cubical.Tactics.Reflection.QuoteCubical
open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.CuTerm

open import Cubical.Tactics.PathSolver.Degen
open import Cubical.Tactics.PathSolver.MonoidalSolver.PathEval
open import Cubical.Tactics.PathSolver.Path

private
  variable
    ℓ : Level
    A B : Type ℓ





flipOnFalse : Bool → R.Term → R.Term
flipOnFalse b t = if b then t else R.def (quote ~_) v[ t ]



data 1DimView (A : Type ℓ) : Type ℓ where
 [_]1d : A → 1DimView A
 [_∙∙1d_∙∙1d_]1d : 1DimView A → 1DimView A → 1DimView A → 1DimView A




map-1DimView : (f : A → B) → 1DimView A → 1DimView B
map-1DimView f [ x ]1d = [ f x ]1d
map-1DimView f [ x ∙∙1d x₁ ∙∙1d x₂ ]1d = [ (map-1DimView f x) ∙∙1d (map-1DimView f x₁) ∙∙1d (map-1DimView f x₂) ]1d



module _ {M : Functorω} {{_ : RawApplicative M}} {{_ : RawMonad M}} where

 mapM-1DimView : (f : A → M B) → 1DimView A → M (1DimView B)
 mapM-1DimView f [ x ]1d = ⦇ [ f x ]1d ⦈
 mapM-1DimView f [ x ∙∙1d x₁ ∙∙1d x₂ ]1d =
   ⦇ [ (mapM-1DimView f x) ∙∙1d (mapM-1DimView f x₁) ∙∙1d (mapM-1DimView f x₂) ]1d ⦈


sym1DimView : 1DimView (A × R.Term) → 1DimView (A × R.Term)
sym1DimView [ (a , x) ]1d = [ (a , (invVar zero x)) ]1d
sym1DimView [ x ∙∙1d x₁ ∙∙1d x₂ ]1d =
  [ (sym1DimView x₂) ∙∙1d (sym1DimView x₁) ∙∙1d (sym1DimView x) ]1d

module _ (a : A) where
 to1DimView :  CuTerm' ⊥ A → Maybe (1DimView (A × R.Term))

 to1DimView (hco (((just b) ∷ [] , fc) ∷ ((just b') ∷ [] , fc') ∷ []) x₁) =
   (do x₁ ← to1DimView x₁
       f ← to1DimView fc
       f' ← to1DimView fc'
       let f0 = if b then f' else f
       let f1 = if b then f else f'
       just [ sym1DimView f0 ∙∙1d x₁ ∙∙1d f1 ]1d)


 to1DimView (cell' x x₁) = just [ (x , x₁) ]1d
 to1DimView _ = nothing


1dvEnd : 1DimView (A × R.Term) → R.TC PathTerm
1dvEnd y@([ (_ , x) ]1d) = 𝒓efl <$> (addNDimsToCtx 1 $ R.normalise
          (replaceVarWithCon (λ { zero → just (quote i1) ; _ → nothing }) x))
1dvEnd y@([ x ∙∙1d x₁ ∙∙1d x₂ ]1d) = 1dvEnd x₂



fill1DV' : 1DimView (Maybe (R.Term × R.Term) × PathTerm) → PathTerm →  R.TC (R.Term × PathTerm)
fill1DV' [ nothing , p ]1d q = do
  (q , squareTerm s) ← p ↙ q
  pure (s , q)
fill1DV' [ just (_ , ud≡) , p ]1d q = do
  (q , squareTerm s) ← p ↙ q
  pure (R.def (quote comp₋₀) (s v∷ v[ vlam "𝓳" $ vlam "𝓲" ud≡ ])  , q)
fill1DV' [ p₀ ∙∙1d p₁ ∙∙1d p₂ ]1d q = do
  (s₂ , q) ← fill1DV' p₂ q
  (s₁ , q) ← fill1DV' p₁ q
  (s₀ , q) ← fill1DV' p₀ q
  pure (R.def (quote _∙∙■_∙∙■_) (s₀ v∷ s₁ v∷ v[ s₂ ]) , q )

fill1DV : 1DimView (A × R.Term) → R.TC (R.Term × PathTerm)
fill1DV x =

  1dvEnd x >>= (fill1DV' (map-1DimView (λ (_ , pt) → nothing ,  asPathTerm pt) x))



quote1D : Maybe R.Type → R.Term → R.TC ((Maybe R.Term) × 1DimView (Maybe (R.Term × R.Term) × R.Term))
quote1D mbty t = do
  cu ← extractCuTermFromPath mbty t
  let cu' = appCongs 1 cu
  congPa ← pure (ToTerm.toTerm (defaultCtx 2) (fillCongs 100 1 cu))
  let mbCongPa = if (hasVar 1 congPa) then just congPa else nothing
  Mb.rec (R.typeError [ "imposible in simplifyPath" ]ₑ)
               (λ (x , y) → x ,_ <$> mapM-1DimView (UndegenCell.mbUndegen' 1 ∘S snd) y)
               (map-Maybe  (mbCongPa ,_) (to1DimView _ cu'))



simplifyFillTerm : Maybe R.Type → R.Term → R.TC R.Term
simplifyFillTerm mbTy t = do
  (_ , 1dv) ← quote1D  mbTy t
  (s , _) ← fill1DV 1dv
  pure s
  -- (R.typeError $ [ s ]ₑ)



macro
 simplifyFill : R.Term → R.Term → R.TC Unit
 simplifyFill t h = do
   sq ← simplifyFillTerm nothing t
   R.unify sq h

 simplifyPath : R.Term → R.Term → R.TC Unit
 simplifyPath t h = do
   sq ← simplifyFillTerm nothing t
   R.unify (R.def (quote ◪→≡) v[ sq ]) h

stepSq : R.Type → R.Term → Maybe PathTerm →  R.TC (R.Term × PathTerm)
stepSq A p mbQ = do
  (mbCong≡ , 1dt) ← quote1D (just A) $ vlam "𝒾" p

  q ← Mb.rec (1dvEnd 1dt) pure mbQ
  (s , q') ←  fill1DV' (map-1DimView (map-snd asPathTerm) 1dt ) q

  let s' = Mb.rec s
            (λ c≡ → R.def (quote comp₋₀) (s v∷ v[ vlam "𝓳" $ vlam "𝓲" c≡ ]))
            mbCong≡
  pure $ s' , q'


_$sp_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → A → B
f $sp a = f a

macro


 solvePaths : R.Term → R.TC Unit
 solvePaths h = R.withReduceDefs (false , quote _$sp_ ∷ [ quote ua ]) do
  hTy ← R.inferType h >>= wait-for-term >>= R.normalise
  bdTM@(A , ((a₀₋ , a₁₋) , (a₋₀ , a₋₁))) ← (matchSquare <$> matchNCube hTy) >>=
     Mb.rec (R.typeError [ "not a square" ]ₑ) pure
  (a₁₋' , p₁₀) ← stepSq A a₁₋ nothing
  (a₋₁' , p₀₁) ← stepSq A a₋₁ nothing
  (a₀₋' , _) ← stepSq A a₀₋ (just p₀₁)
  (a₋₀' , _) ← stepSq A a₋₀ (just p₁₀)

  let solution = R.def (quote ◪mkSq)
        (a₀₋' v∷ a₁₋' v∷ a₋₀' v∷ a₋₁' v∷ [])

  R.unify solution h <|> R.typeError [ solution ]ₑ

