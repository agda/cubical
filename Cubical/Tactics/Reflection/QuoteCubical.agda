{-

## Cubical.Tactics.Reflection.QuoteCubical

This module provides functionality for reflecting cubical terms within Agda, focusing on handling higher-dimensional compositions. It leverages the capabilities defined in `Cubical.Tactics.Reflection.CuTerm` to extract cubical terms.

### Main Types and Functions:

* `MarkHCompsVar`:
  * A marker datatype used internally to handle `hcomp` terms during reflection.

* `traceHComps`:
  * Given a term, it traces and encodes `hcomp` terms, substituting them with a marker.
  * Returns either a string message in case of error or a pair of the transformed term and the list of identified `hcomp` terms.

#### Internal Monad `M`:
  * Composed of states and error management, used to encapsulate reflection operations.

#### Functions for Encoding and Decoding `hcomp` Terms:
  * `codeHcomps`: Encodes `hcomp` terms by replacing them with a marker (`markHCompsVar`).
  * `decodeHcomps`: Decodes `hcomp` markers back to their original term representations.


### Extraction and Evaluation:

* `extractCuTerm'`:
  * Extracts cubical terms recursively, handling `hcomp` and `𝒄ong` constructions based on specified depth and dimension parameters.
  * Uses auxiliary functions like `checkHcomp` to handle `hcomp` terms and `try𝒄ong` to manage `𝒄ong` terms.

* `quoteCuTerm` and `extractCuTerm`:
  * Wrappers around `extractCuTerm'` to initiate extraction with a default depth of 100.

* `pathApp` and `pathAppN`:
  * Utility functions to apply a term along a path, handling various term constructions recursively.

### Boundary Matching and Normalization:

* `matchNCubeF`, `matchNCubeP`, and `matchNCube`:
  * Match types od higher-dimensional cubes (n-cubes) and reduce them to their boundary terms.

* `NBoundaryTerm`:
  * Represents terms at the boundaries of cubes, encapsulating a term and its list of boundaries.

* `quoteBd` and `quoteBdNC`:
  * Quote the boundaries of n-cubes to CuTerm representation.


### Utilities for Extracting and Displaying Cubical Terms:

* `extractCuTermFromNPath`: Extracts cubical terms from n-path terms, calculating the appropriate dimension.

* `showCuTerm` and `showCuCode` (macros):
  * Display structured or code representation of cubical terms for a given term and its inferred type.


-}

{-# OPTIONS --safe #-}
module Cubical.Tactics.Reflection.QuoteCubical where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude


open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order.Recursive as ℕOR
open import Cubical.Data.Empty

open import Cubical.Reflection.Base renaming (v to 𝒗)
open import Cubical.Reflection.Sugar
import Agda.Builtin.Reflection as R
open import Agda.Builtin.String

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Utilities

open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection.Error

open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.CuTerm

open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)

data MarkHCompsVar : Type where
 markHCompsVar : MarkHCompsVar

traceHComps : R.Term → String ⊎.⊎ (R.Term × List R.Term)
traceHComps t =
   let (x , xs) = runIdentity (unwrap (unwrap (codeHcomps t)) [])
   in ⊎.map (idfun _)
         ((_, xs) ∘S decodeHcomps (length xs) ∘S liftVarsFrom (length xs) 0) x

 where

 M : Functorω
 M = [ Plus₀T String RMT  [ State₀T (List R.Term) RMT IdentityF ]_ ]_


 codeHcomps : R.Term → M (R.Term)
 codeHcomps = atVarOrDefM.rv
   (λ n k args argsM → R.var k <$> argsM)
   atDef
   zero
   where
   atDef : ℕ → R.Name → (List (R.Arg R.Term)) → M (List (R.Arg R.Term)) → M R.Term
   atDef n (quote hcomp) args _ = do
     s ← liftM get
     liftM (modify (_∷ʳ R.def (quote hcomp) args))
     pure (R.def (quote markHCompsVar) v[ R.lit (R.nat (length {A = R.Term} s)) ])
   atDef _ nm _ argsM = R.def nm <$> argsM

 decodeHcomps : ℕ → R.Term → R.Term
 decodeHcomps m = runIdentity ∘S
   atVarOrDefM.rv
    (λ _ v _ → R.var v <$>_)
    (λ n → λ where
      (quote markHCompsVar) v[ R.lit (R.nat v) ] _ →  pure $ R.var (v + n) []
      nm _ → R.def nm <$>_) zero

normaliseWithType : R.Type → R.Term  → R.TC R.Term
normaliseWithType ty tm = R.withNormalisation true $ R.checkType tm ty

module ECT where

 evalOp : (Maybe R.Type) → ℕ → R.Term → R.TC R.Term
 evalOp mbTy dims =
    Mb.rec R.normalise (normaliseWithType ∘S liftVarsFrom dims zero) mbTy


 getCuCase : R.Term → R.TC (Maybe ((R.Term × R.Term × R.Term × R.Term) × IExpr))
 getCuCase (R.def (quote hcomp) ( _ h∷ A h∷ φTm h∷ fcs v∷ v[ cap ])) = do
   R.debugPrint "getCuCaseφ" 5 $ "getCuCase' φ :" ∷ₑ [ φTm ]ₑ
   (just ∘ ((A , φTm , fcs , cap) ,_))  <$> extractIExprM φTm
 getCuCase _ = pure nothing


 try𝒄ong : ℕ → ℕ → R.Term → R.TC (Maybe (R.Term × List (CuTerm)))

 checkHcomp : Maybe R.Type → ℕ → ℕ → R.Term → R.Term → R.Term → R.Term → FExpr → R.TC CuTerm

 extractCuTerm' : Maybe R.Type → ℕ → ℕ → R.Term → R.TC CuTerm

 checkHcomp mbTy zero _ _ _ _ _ _ = R.typeError [ "checkHcomp FAIL : max depth" ]ₑ
 checkHcomp mbTy (suc m) dim A φTm fcs lid φ = do
   ⦇ hco
      (mapM (λ sf → do
           let tmA = subfaceCell sf fcs
               Atm = subfaceCell sf A
               -- tmA' = replaceVarWithCon (λ { zero → just (quote i0) ; _ → nothing }) fcs
               tmB = (R.def (quote $PI) ((liftVars Atm) v∷ ((liftVars tmA))
                       v∷ v[ R.var zero [] ] ))
               sfbo = tmB

           ⦇ ⦇ sf ⦈ , (extractCuTerm' mbTy  m (suc (sfDim sf)) sfbo) ⦈
           ) φ)
      ((addNDimsToCtx dim (evalOp mbTy dim lid)) >>= extractCuTerm' mbTy m dim) ⦈




 try𝒄ong zero _ _ = R.typeError [ "extractCuTerm FAIL : max depth" ]ₑ

 try𝒄ong (suc m) dim t = do
   ⊎.rec (R.typeError ∘S [_]ₑ)
    withTracing
    (traceHComps t)
   where

   withTracing : R.Term × List R.Term → R.TC (Maybe (R.Term × List (CuTerm)))
   withTracing (_ , []) = pure nothing
   withTracing (R.var zero [] , _) = pure nothing
   withTracing (h , tl) = ⦇ just ⦇ ⦇ h ⦈ , (mapM (extractCuTerm' nothing m dim) tl) ⦈  ⦈

 extractCuTerm' mbTy zero _ _ = R.typeError [ "extractCuTerm FAIL : max depth" ]ₑ
 extractCuTerm' mbTy (suc m) dim t = do
   t ← addNDimsToCtx dim $ evalOp mbTy dim t

   addNDimsToCtx dim (getCuCase t) >>=
    Mb.rec ( (pure t )
             >>= λ t' → --R.debugPrint "checkHcomp" 4 ("cell: \n " ∷ₑ [ tt ]ₑ) >>
               (  try𝒄ong m dim t' ) >>= pure ∘S Mb.rec (cell t') (uncurry 𝒄ongF)
               )
           λ ((A , φTm , fcs , cap) , φ) →
                 (checkHcomp
                     mbTy
                     -- (just (Mb.fromMaybe A mbTy))
                     m dim A φTm fcs cap (L.map (offsetR nothing dim) (I→F φ)))



quoteCuTerm : Maybe R.Type → ℕ →  R.Term → R.TC CuTerm
quoteCuTerm = flip ECT.extractCuTerm' 100

extractCuTerm : Maybe R.Type → ℕ → R.Term → R.TC CuTerm
extractCuTerm mbTy dim = ECT.extractCuTerm' mbTy  100 dim ∘S appNDimsI dim ∘S liftVarsFrom dim 0



pathApp : R.Term → R.Term
pathApp (R.var x₁ args) = R.var (suc x₁)  $ (LiftFrom.ra 1 0 args) ++ v[ 𝒗 zero ]
pathApp (R.con c args) = R.con c $ (LiftFrom.ra 1 0 args) ++ v[ 𝒗 zero ]
pathApp (R.def f args) = R.def f $ (LiftFrom.ra 1 0 args) ++ v[ 𝒗 zero ]
pathApp (R.lam v (R.abs _ t)) = t
pathApp (R.pat-lam cs args) =
 R.pat-lam (LiftFrom.rc 1 0 cs) $ (LiftFrom.ra 1 0 args) ++ v[ 𝒗 zero ]
pathApp (R.pi a b) = R.lit (R.string ("unexpected in pathApp"))
pathApp (R.agda-sort s) = R.lit (R.string ("unexpected in pathApp"))
pathApp (R.lit l) = R.lit (R.string ("unexpected in pathApp"))
pathApp (R.meta x₁ args) = R.meta x₁ $ (LiftFrom.ra 1 0 args) ++ v[ 𝒗 zero ]
pathApp R.unknown = R.unknown

extractCuTermFromPath : Maybe R.Type → R.Term → R.TC CuTerm
extractCuTermFromPath mbTy = ECT.extractCuTerm' mbTy  100 1 ∘S pathApp


pathAppN : ℕ → R.Term → R.Term
pathAppN = flip iter pathApp

NBoundaryTerm : Type
NBoundaryTerm = (R.Term × List (R.Term × R.Term))


matchNCubeF : ℕ → R.Term → R.TC NBoundaryTerm
matchNCubeF (suc fuel) (R.def (quote PathP) (l h∷ T v∷ x v∷ y v∷ [])) = do
  (T' , xs) ←
       (addNDimsToCtx 1 $
        (do T' ←  R.normalise $ appNDimsI 1 (liftVars T)
            matchNCubeF fuel T'))
  let d = (length xs)
      T0 = replaceAtTrm d (endTerm false) T'
      T1 = replaceAtTrm d (endTerm true) T'
  -- let
  x' ← (addNDimsToCtx d $ normaliseWithType (T0) $ pathAppN d x) -- <|> R.typeError [ "matchNCubeF T0" ]ₑ
  y' ← (addNDimsToCtx d $ normaliseWithType (T1) $ pathAppN d y) -- <|> R.typeError [ "matchNCubeF T1" ]ₑ
  pure (T' , (x' , y') ∷ xs)
matchNCubeF _ tm = (pure $ tm , [])

matchNCubeP matchNCube : R.Term → R.TC NBoundaryTerm
matchNCubeP = matchNCubeF 20

matchNCube x = do
 (A , fcs) ← matchNCubeF 20 x
 if (hasVarBy (_<ℕ length fcs) A) then R.typeError [ "not a _≡_ " ]ₑ else
  pure ((dropVars.rv (length fcs) zero A , fcs))

quoteBd : NBoundaryTerm → R.TC CuBoundary
quoteBd (A , xs) = do
 let dim = predℕ (length xs)
 mapM (λ (t0 , t1) → ⦇ quoteCuTerm (just A) dim t0 , quoteCuTerm (just A) dim t1 ⦈ ) xs


matchSquare : NBoundaryTerm → Maybe (R.Term × ((R.Term × R.Term)×(R.Term × R.Term)))
matchSquare (A , ((a₀₋ , a₁₋) ∷ (a₋₀ , a₋₁) ∷ [])) =
  just (A , ((a₀₋ , a₁₋) , (a₋₀ , a₋₁)))
matchSquare _ = nothing

unquoteNCube : NBoundaryTerm → R.Type
unquoteNCube (A , []) = A
unquoteNCube (A , (f0 , f1) ∷ fcs) =
 let t = unquoteNCube (A , fcs)
 in R.def (quote PathP)
     (vlam "𝒊" t v∷ vlamⁿ (length fcs) f0 v∷ v[ vlamⁿ (length fcs) f1 ])

rotK : ℕ → ℕ → Maybe ℕ
rotK k n with n ℕOR.≟ k
... | lt x = just (suc n)
... | eq x = just zero
... | gt x = nothing

rotVars : ℕ → R.Term → R.Term
rotVars k = replaceVarWithTerm (map-Maybe 𝒗 ∘S rotK k)

allTrue : List Bool → Bool
allTrue = foldl _and_ true

any? : List Bool → Bool
any? [] = false
any? (false ∷ x₁) = any? x₁
any? (true ∷ x₁) = true

mbEquation : NBoundaryTerm → Maybe (R.Term × R.Term)
mbEquation (A , []) = nothing
mbEquation (A , x ∷ xs) =
 if (allTrue (join $ L.map (λ t → (L.map (not ∘S flip hasVar t ) ([ predℕ (length xs) ])))
   $ join $ L.map (λ (x , y) → x ∷ [ y ]) xs))
 then just x
 else nothing


nCubeToEq : NBoundaryTerm → R.TC NBoundaryTerm
nCubeToEq (A , []) = pure $ A , []
nCubeToEq (A , (f0 , f1) ∷ xs) = (A ,_) <$> do
 let f0' = ToTerm.toTerm {Unit} {Unit} (defaultCtx  (length xs))
         (hco (join $ L.map (λ (k , (x , y)) →
                      ((rev $ L.insertAt k (just false) (repeat (predℕ (length xs)) nothing))
                        , cell (rotVars (predℕ $ length xs) $ x))
                  ∷ [ ((rev $ L.insertAt k (just true) (repeat (predℕ (length xs)) nothing))
                        , cell (rotVars (predℕ $ length xs) $ y)) ])
                (L.zipWithIndex xs))
           (cell f0))

 addNDimsToCtx (length xs) $ ⦇ pure (f0' ,  f1 ) ∷
    (mapM (λ (x , y) →
         ⦇ R.reduce (subfaceCellNoDrop (repeat (predℕ $ length xs) (nothing) ∷ʳ just true) x )
         , R.reduce (subfaceCellNoDrop (repeat (predℕ $ length xs) (nothing) ∷ʳ just true) y )
         ⦈)
         xs) ⦈

nCubeToEqPath : NBoundaryTerm → R.Term
nCubeToEqPath (A , []) = q[ refl ]
nCubeToEqPath (A , (f0 , f1) ∷ xs) =
  let dim = (length xs)
  in vlamⁿ (suc dim) (ToTerm.toTermFill' {Unit} {Unit} (defaultCtx dim)
         (hcodata (join $ L.map (λ (k , (x , y)) →
                      ((rev $ L.insertAt k (just false) (repeat (predℕ (length xs)) nothing))
                        , cell (rotVars (predℕ $ length xs) $ x))
                  ∷ [ ((rev $ L.insertAt k (just true) (repeat (predℕ (length xs)) nothing))
                        , cell (rotVars (predℕ $ length xs) $ y)) ])
                (L.zipWithIndex xs))
           (cell f0)))

faceSubFace : ℕ → (Bool × ℕ) → SubFace
faceSubFace dim (b , k) =
  take k (repeat (predℕ dim) nothing)
  ++ [ just b ] ++
  drop k (repeat (predℕ dim) nothing)



tryCastAsNoCongM : CuTerm → R.TC (CuTerm' ⊥ Unit)
tryCastAsNoCongM = fromJust [ "failed to cast as no cong" ]ₑ ∘S tryCastAsNoCong


quoteCuTermNC : Maybe R.Type → ℕ →  R.Term → R.TC CuTermNC
quoteCuTermNC mbty dim = quoteCuTerm mbty dim >=> tryCastAsNoCongM

extractCuTermNC : Maybe R.Type → ℕ → R.Term → R.TC CuTermNC
extractCuTermNC mbTy dim =
   (ECT.extractCuTerm' mbTy  100 dim ∘S appNDimsI dim ∘S liftVarsFrom dim 0)
     >=> tryCastAsNoCongM


quoteBdNC : NBoundaryTerm → R.TC (CuBoundary' ⊥ Unit)
quoteBdNC (A , xs) = do
 let dim = predℕ (length xs)
 mapM (λ (t0 , t1) → ⦇ quoteCuTermNC (just A) dim t0 , quoteCuTermNC (just A) dim t1 ⦈ ) xs




extractCuTermFromNPath : R.Type → R.Term → R.TC (ℕ × CuTerm)
extractCuTermFromNPath ty tm = do
 (A , dim) ← map-snd length <$> matchNCube ty
 (dim ,_) <$> ECT.extractCuTerm'
     (just A)
     100 dim (pathAppN dim tm)


macro
 showCuTerm : R.Term → R.Term → R.TC Unit
 showCuTerm t h = do
  hTy ← R.inferType t >>= wait-for-term >>= R.normalise
  (dim , cu) ← extractCuTermFromNPath hTy t
  te ← ppCT dim 100 cu
  R.typeError te

 showCuCode : R.Term → R.Term → R.TC Unit
 showCuCode t h = do
  hTy ← R.inferType t >>= wait-for-term >>= R.normalise
  (dim , cu) ← extractCuTermFromNPath hTy t
  c ← codeGen false dim 100 cu
  R.typeError [ c ]ₑ
