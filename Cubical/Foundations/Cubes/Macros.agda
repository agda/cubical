{-

The Internal n-Cubes

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Cubes.Macros where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.2LTT
open import Cubical.Foundations.Cubes.HLevels
open import Cubical.Foundations.Cubes.External

open import Cubical.Data.Nat.Base

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.List
open import Cubical.Reflection.Base

private
  variable
    ℓ : Level
    A : Type ℓ


-- Transform between external and internal cubes

private
  add2Impl : List (Arg Term) →  List (Arg Term)
  add2Impl t =
    harg {quantity-ω} unknown ∷
    harg {quantity-ω} unknown ∷ t

macro

  fromCube : (n : ℕ) → Term → Term → TC Unit
  fromCube 0 p t = unify p t
  fromCube (suc n) p t = unify t
    (def (quote Cube→ΠCubeᵉ) (add2Impl (ℕ→ℕᵉTerm (suc n) v∷ p v∷ [])))

  toCube : (n : ℕ) → Term → Term → TC Unit
  toCube 0 p t = unify p t
  toCube (suc n) p t = unify t
    (def (quote ΠCubeᵉ→Cube) (add2Impl (ℕ→ℕᵉTerm (suc n) v∷ p v∷ [])))

  from∂Cube : (n : ℕ) → Term → TC Unit
  from∂Cube 0 t = typeError
    (strErr "Only work for n>0." ∷ [])
  from∂Cube (suc n) t = unify t
    (def (quote ∂Cube→∂ΠCubeᵉ) (add2Impl (ℕ→ℕᵉTerm (suc n) v∷ [])))

  to∂Cube : (n : ℕ) → Term → TC Unit
  to∂Cube 0 t = typeError
    (strErr "Only work for n>0." ∷ [])
  to∂Cube (suc n) t = unify t
    (def (quote ∂ΠCubeᵉ→∂Cube) (add2Impl (ℕ→ℕᵉTerm (suc n) v∷ [])))


-- To fill cubes under h-level assumptions

fillCubeSuc :
  (n : ℕᵉ) (h : isOfHLevel (ℕᵉ→ℕ (suc n)) A)
  (u : ∂ΠCubeᵉ (suc n) A) → _
fillCubeSuc n h u =
  let ∂ = ∂ΠCubeᵉ→∂Cube (suc n) u in
  CubeRel→ΠCubeRelᵉ (suc n) ∂ (isOfHLevel→isCubeFilled (ℕᵉ→ℕ (suc n)) h ∂)

macro
  fillCube : (n : ℕ) → Term → TC Unit
  fillCube 0 t = typeError
    (strErr "Only work for n>0." ∷ [])
  fillCube (suc n) t = unify t
    (def (quote fillCubeSuc) (add2Impl (ℕ→ℕᵉTerm n v∷ [])))
