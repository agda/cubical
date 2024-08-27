{-
This module serves as an experimental demonstration of the potential usage of cubical-flavored reflection machinery. It focuses on transforming terms to a form where all interval expressions are either `i0`, `i1`, or a single interval variable (This transformation excludes the implicit `φ` argument of `hcomp`, which is effectively a face expression), effectively mimicking the Cartesian cubical theory.

### Example Transformations

- **`cpfCC`**: Demonstrates the transformation on a compPath-filler.
- **`assocCC`**: Demonstrates the transformation on a paths associativity.
- ** `rot-refl'CC`**: Examples of transformed cubes.
-}

{-# OPTIONS --safe #-}
module Cubical.Tactics.PathSolver.CartesianExperiment where


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


private
  variable
    ℓ : Level


-- really just refl ∙_
reComp : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → x ≡ y
reComp p i =
  hcomp {φ = i ∨ ~ i} (λ k _ → (p (i ∧ k))) (p i0)

--  really just lUnit
reFill : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ reComp p
reFill p j i =
  hcomp {φ = i ∨ ~ i ∨ ~ j} (λ k _ → (p (i ∧ k))) (p i0)


addConstSubfaces : ℕ → CuTermNC → R.TC CuTermNC
addConstSubfaces = h
 where

 addMiss : ℕ → List (SubFace × CuTermNC) → CuTermNC → R.TC (List (SubFace × CuTermNC))
 addMiss dim xs xb = do
   newSfs ← catMaybes <$> mapM mbTermForFace msf
   pure (newSfs ++fe× xs)
  where
   msf = missingSubFaces dim (L.map fst xs)

   mbTermForFace : SubFace → R.TC (Maybe (SubFace × CuTermNC))
   mbTermForFace sf =  do
     cOnSF ← cuEvalN sf (hco xs xb)
     if (allCellsConstant? (suc (sfDim sf)) cOnSF)
      then pure $ just (sf , cell (liftVars (mostNestedCap cOnSF)))
      else ⦇ nothing ⦈

 h : ℕ → CuTermNC → R.TC CuTermNC
 hh : List (SubFace × CuTermNC) → R.TC (List (SubFace × CuTermNC))

 h dim (hco x x₁) = do
  x' ← hh x
  xb ← (h dim x₁)
  ⦇ hco (addMiss dim x' xb) ⦇ xb ⦈ ⦈
 h dim (cell' x x₁) = pure $ cell' x x₁
 h dim (𝒄ong' x x₁) = R.typeError [ "notImplemented" ]ₑ

 hh [] = ⦇ [] ⦈
 hh ((sf , x) ∷ xs) =
   ⦇ ⦇ ⦇ sf ⦈ , h (suc (sfDim sf)) x ⦈ ∷ (hh xs) ⦈


module unConnect (do-fill : Bool) where

 unConnCell : ℕ → R.Term → R.Term → R.TC CuTermNC
 unConnCell dim jT (R.var k (z₀ v∷ v[ z₁ ])) =
   (if do-fill then (pure ∘S cell)
     else (quoteCuTermNC nothing dim >=> addConstSubfaces dim))
     (R.def (quote reFill)
       (vlam "𝒾"
       ((R.def (quote reFill) (R.var (suc k) v[ 𝒗 zero ] v∷ (liftVars jT) v∷ v[ liftVars z₁ ])))
        v∷ jT v∷  v[ z₀ ]))

 unConnCell dim jT (R.var k v[ z ]) =
   (if do-fill then (pure ∘S cell) else (quoteCuTermNC nothing dim))
     (R.def (quote reFill) ((R.var k []) v∷ jT v∷ v[ z ]))
 unConnCell _ _ t = pure $ cell' _ t


 unConnS : List (SubFace × CuTermNC) → R.TC (List (SubFace × CuTermNC))

 unConnA : ℕ → List (Hco ⊥ Unit) → R.TC (List (Hco ⊥ Unit))


 unConn : ℕ → CuTermNC → R.TC (CuTermNC)
 unConn dim (hco x x₁) = ⦇ hco (unConnS x) (unConn dim x₁) ⦈
 unConn dim (cell' x x₁) =
   if do-fill
   then unConnCell (suc dim) (𝒗 dim) (liftVarsFrom (suc zero) dim x₁)
   else unConnCell dim (endTerm true) x₁
 unConn dim (𝒄ong' {cg = cg} x x₁) = 𝒄ong' {cg = cg} x <$> unConnA dim x₁

 unConnS [] = ⦇ [] ⦈
 unConnS ((sf , x) ∷ xs) = ⦇ ⦇ ⦇ (sf ++ (if do-fill then [ nothing ] else [])) ⦈
  , unConn (suc (sfDim sf)) x ⦈ ∷ unConnS xs ⦈

 unConnA _ [] = ⦇ [] ⦈
 unConnA dim (hcodata x x₁ ∷ xs) = ⦇ ⦇ hcodata (unConnS x) (unConn dim x₁) ⦈ ∷ (unConnA dim xs) ⦈



unConn = unConnect.unConn false
unConnFill = unConnect.unConn true


module _ (dim : ℕ) where
 macro
  unConnTest : R.Term → R.Term → R.TC Unit
  unConnTest t h = do
   cu ← (extractCuTermNC nothing dim t)
   cu' ← unConn dim cu
   te0 ← ppCT dim 100 cu
   te0' ← ppCT dim 100 cu'
   wrapError h $
          "input:" ∷nl (indentₑ 4 te0)
     ++nl "\n∨,∧,~ - removed :" ∷nl (indentₑ 4 te0')

  unConnTest'' : R.Term → R.Term → R.TC Unit
  unConnTest'' t h = do
   cu ← (extractCuTermNC nothing dim t)
   cu' ← unConn dim cu
   te0 ← ppCT dim 100 cu
   te0' ← ppCT dim 100 cu'
   R.typeError te0'

  unConnM : R.Term → R.Term → R.TC Unit
  unConnM t h = do
   cu ← (extractCuTermNC nothing dim t)
   cu' ← unConn dim cu
   R.unify (toTerm dim cu') h

  unConnM≡ : R.Term → R.Term → R.TC Unit
  unConnM≡ t h = do
   cu ← (extractCuTermNC nothing dim t)
   cu' ← unConnFill dim cu
   let cu'T = toTerm (suc dim) cu'
   -- cu'' ← R.checkType cu'T (R.def (quote PathP) (R.unknown v∷ R.unknown v∷ v[ R.unknown ]))
   R.unify cu'T h



module _ {A : Type ℓ} {x y z w : A} (p : x ≡ y)(q : y ≡ z)(r : z ≡ w) where

 cpfCC : ResultIs
        ("input:                                       " ∷
         "                                             " ∷
         "     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₀                              " ∷
         "     ║  (𝓲₀=0) → q 𝓲₁                        " ∷
         "     ║  (𝓲₁=0) → p (~ 𝓲₀ ∨ ~ 𝒛₀)             " ∷
         "     ║  (𝓲₁=1) → r (𝓲₀ ∧ 𝒛₀)                 " ∷
         "     ├───────────                            " ∷
         "     │ q 𝓲₁                                  " ∷
         "     └───────────                            " ∷
         "∨,∧,~ - removed :                            " ∷
         "                                             " ∷
         "     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₀                              " ∷
         "     ║  (𝓲₀=0) →                             " ∷
         "     ║     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₁                        " ∷
         "     ║     ║  (𝓲₁=0) → y                     " ∷
         "     ║     ║  (𝓲₁=1) → q 𝒛₁                  " ∷
         "     ║     ├───────────                      " ∷
         "     ║     │ y                               " ∷
         "     ║     └───────────                      " ∷
         "     ║  (𝓲₁=0) →                             " ∷
         "     ║     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₁                        " ∷
         "     ║     ║  (𝒛₀=1)(𝓲₀=1) → x               " ∷
         "     ║     ║  (𝒛₀=0)       → p 𝒛₁            " ∷
         "     ║     ║  (𝓲₀=0)       → p 𝒛₁            " ∷
         "     ║     ├───────────                      " ∷
         "     ║     │ x                               " ∷
         "     ║     └───────────                      " ∷
         "     ║  (𝓲₁=1) →                             " ∷
         "     ║     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₁                        " ∷
         "     ║     ║  (𝒛₀=0)       → z               " ∷
         "     ║     ║  (𝓲₀=0)       → z               " ∷
         "     ║     ║  (𝒛₀=1)(𝓲₀=1) → r 𝒛₁            " ∷
         "     ║     ├───────────                      " ∷
         "     ║     │ z                               " ∷
         "     ║     └───────────                      " ∷
         "     ├───────────                            " ∷
         "     │                                       " ∷
         "     │ 𝒉𝒄𝒐𝒎𝒑 λ 𝒛₀                            " ∷
         "     │ ║  (𝓲₁=0) → y                         " ∷
         "     │ ║  (𝓲₁=1) → q 𝒛₀                      " ∷
         "     │ ├───────────                          " ∷
         "     │ │ y                                   " ∷
         "     │ └───────────                          " ∷
         "     └───────────                            " ∷ [])
 cpfCC = unConnTest (suc (suc zero)) λ (i j : I) → doubleCompPath-filler p q r i j

 assocCC : Square _ _ _ _
 assocCC = unConnM (suc (suc zero)) λ (i j : I) → assoc p q r i j



module Sq-rot-refl {A : Type ℓ}
  {a : A}
  (s : Square {a₀₀ = a} refl refl refl refl) where

  rot-refl : Cube
         s (λ i j → s j (~ i))
         refl refl
         refl refl
  rot-refl k i j =
    hcomp (λ l → λ { (i = i0) → s (~ l) (j ∨ k)
                   ; (i = i1) → a
                   ; (j = i0) → s (~ l) (~ i ∧ k)
                   ; (j = i1) → a
                   ; (k = i0) → s (i ∨ ~ l) j
                   ; (k = i1) → s (j ∨ ~ l) (~ i)
                   })
          a



  rot-refl' : s ≡ λ i j → s j (~ i)
  rot-refl' t i j =
    hcomp (λ l → λ { (t = i0) → s i j
                   ; (t = i1) → s j (~ i)
                   ; (i = i0) → s (~ l ∧ t ∧ j) ((~ t ∧ j) ∨ t ∨ j)
                   ; (i = i1) → s ((~ l ∧ ~ t ∨ (t ∧ j) ∨ j) ∨ l ∨ ~ t ∨ (t ∧ j) ∨ j) (~ t ∧ j)
                   ; (j = i0) → s (~ l ∧ ~ t ∧ i) (t ∧ ~ i)
                   ; (j = i1) → s ((~ l ∧ (~ t ∧ i) ∨ t ∨ i) ∨ l ∨ (~ t ∧ i) ∨ t ∨ i)
                                  (~ t ∨ (t ∧ ~ i) ∨ ~ i)
                   })
          (s ((~ t ∧ i) ∨ (t ∧ j) ∨ i ∧ j) ((~ t ∧ j) ∨ (t ∧ ~ i) ∨ j ∧ ~ i))


  s' : Square {a₀₀ = a} refl refl refl refl
  s' = unConnM (suc (suc zero)) (λ (i j : I) → s i j)

  s'-rot : Square {a₀₀ = a} refl refl refl refl
  s'-rot = unConnM (suc (suc zero)) (λ (i j : I) → s j (~ i))


  rot-refl'CC : s' ≡ s'-rot
  rot-refl'CC = unConnM (suc (suc (suc zero))) λ (z i j : I) → rot-refl' z i j

