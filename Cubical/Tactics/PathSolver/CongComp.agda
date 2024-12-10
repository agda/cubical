{-

This module provides utilities for generalizing the `cong-∙` lemma from `GroupoidLaws.agda`.
The utilities handle multiple arguments (implicit and explicit) and multiple dimensions, applying lemma recursively to subterms at all depths.


- **`appCongs` Module**: Applies a function recursively over composition terms.
- **`fillCongs` Module**: Computes fillers between terms when the function is applied at various levels of the term structure.

-}

{-# OPTIONS --safe #-}
module Cubical.Tactics.PathSolver.CongComp where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma


import Agda.Builtin.Reflection as R
open import Agda.Builtin.String

open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.CuTerm
open import Cubical.Tactics.Reflection.Variables


getSide : ∀ {A} → SubFace → Hco A Unit → CuTerm' A Unit
getSide {A = A}  sf (hcodata l y) =
 Mb.rec
   ((let msf : SubFace × CuTerm' A Unit → Maybe (SubFace × CuTerm' A Unit)
         msf = λ (sf' , t) →
                map-Maybe
                 (λ sf'' → (injSF sf sf'') , cuEval (nothing  ∷ (injSF sf' sf'')) t)
                 (sf' sf∩ sf)
         l' = L.catMaybes (L.map msf l)
         y' = (cuEval sf y)
     in cell (R.lit (R.string "todo in getSide")) )
       )
   ((λ (sf' , f) → f))
  (findBy (⊂⊃? ∘S (sf <sf>_) ∘S fst) l)



module appCongs where

 appCongs : ℕ → ℕ → CuTerm → CuTermNC
 cuCong1 : R.Term → CuTermNC → CuTermNC
 cuCong1L : R.Term → List (SubFace × CuTermNC) → List (SubFace × CuTermNC)
 cuCong1L t [] = []
 cuCong1L t ((sf , x) ∷ xs) =
  (sf , cuCong1 (liftVarsFrom 1 1 (subfaceCell (nothing ∷ sf) t)) x) ∷ cuCong1L t xs

 cuCong1 t (hco x x₁) = hco (cuCong1L t x) (cuCong1 t x₁)
 cuCong1 t (cell x₁) = cell (substTms [ x₁ ] t)

 congCus : ℕ → ℕ → R.Term → List (Hco ⊥ Unit) → CuTermNC
 congCus zero _ _ _ = cell (R.lit (R.string "out of fuel in congCus"))
 congCus (suc fuel) dim t ((hcodata x y) ∷ []) = cuCong1 t (hco x y)
 congCus (suc fuel) dim t xs @(_ ∷ _ ∷ _) = --cell (R.lit (R.string "todo"))
   let lid = appCongs fuel dim (𝒄ongF t  (L.map (CuTermNC→CuTerm  ∘S Hco.bottom) xs))

   in hco (L.map ff sfUnion)  lid
  where
  sfUnion = foldr (_++fe_ ∘S L.map fst ∘S Hco.sides) [] xs

  ff : SubFace → SubFace × CuTerm' ⊥ Unit
  ff sf = sf ,
   let ts = L.map (getSide sf) xs
   in appCongs fuel (suc (sfDim sf))
        (𝒄ongF
        (liftVarsFrom 1 (length xs)
        (subfaceCell ((repeat (length xs) nothing) ++ sf) t)) (L.map CuTermNC→CuTerm ts))

 congCus _ _ t [] = cell t



 appCongsS : ℕ → List (SubFace × CuTerm) → List (SubFace × CuTermNC)
 appCongsS zero _ = []
 appCongsS _ [] = []
 appCongsS (suc fuel) ((sf , x) ∷ xs) =
  (sf , appCongs fuel (suc (sfDim sf)) x) ∷ appCongsS fuel xs

 appCongs zero _ _ = cell (R.lit (R.string "out of fuel in normal𝑪ong"))
 appCongs (suc fuel) dim (hco x x₁) =
   hco (appCongsS fuel x) (appCongs fuel dim x₁)
 appCongs _ dim  (cell' x x₁) = cell' x x₁
 appCongs (suc fuel) dim  (𝒄ong' x x₁) =
   congCus fuel dim x
     (L.map (λ (hcodata sides bottom) →
        hcodata (appCongsS fuel sides) (appCongs fuel dim bottom)) x₁)

appCongs : ℕ → CuTerm → CuTermNC
appCongs = appCongs.appCongs 100


module fillCongs where


 fillCongs : ℕ → ℕ → CuTerm → CuTermNC
 congFill : ℕ → ℕ → R.Term → List (Hco Unit Unit) → CuTermNC
 congFill fuel dim t xs =
   let lid = fillCongs fuel dim $ 𝒄ongF t (L.map (Hco.bottom) xs)
   in hco (((repeat dim nothing ∷ʳ just false)  , f0) ∷
      L.map ff sfUnion)  lid
  where
  sfUnion = foldr (_++fe_ ∘S L.map fst ∘S Hco.sides) [] xs

  ff : SubFace → SubFace × CuTermNC
  ff sf = sf ,
   let ts : List (CuTerm)
       ts = L.map ((getSide sf)) xs
   in fillCongs fuel (suc (sfDim sf)) $
           𝒄ongF  ((liftVarsFrom 1 (length xs)
                (subfaceCell ((repeat (length xs) nothing) ++ sf) t))) ts

  f0 : CuTermNC
  f0 = cell' _ (substTms (
        L.map ((ToTerm.toTermFill {Unit} {Unit} (defaultCtx dim)))
           xs --xs
           ) (liftVarsFrom 1 (length xs) t))

 fillCongsS : ℕ → List (SubFace × CuTerm) → List (SubFace × CuTermNC)

 fillCongs fuel dim (hco x cu) =
   hco (fillCongsS fuel x) (fillCongs fuel dim cu)
 fillCongs fuel dim (cell x₁) = cell (liftVarsFrom 1 dim x₁)
 fillCongs zero dim (𝒄ong' x x₁) = cell (R.lit (R.string "out of fuel in fillCongs"))
 fillCongs (suc fuel) dim (𝒄ong' t []) = cell (liftVarsFrom 1 dim t)
 fillCongs (suc fuel) dim (𝒄ong' t xs) = uncurry (congFill fuel dim) (t , xs)


 fillCongsS fuel [] = []
 fillCongsS fuel ((sf , x) ∷ xs) =
   (sf ∷ʳ nothing , fillCongs fuel (suc (sfDim sf)) x) ∷ fillCongsS fuel xs


open fillCongs using (fillCongs) public
