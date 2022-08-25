{-

Macros about Cubes

Basically they're those operations defined in
`Cubical.Foundations.Cubes.External` and `Cubical.Foundations.Cubes.HLevels`,
but for the convenience of users,
we want to write the internal natural numbers instead of external ones.

The examples are given in `Cubical.Foundations.Cubes`.

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Cubes.Macros where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Cubes.HLevels
open import Cubical.Data.Nat.Base

open import Cubical.Foundations.2LTT
open import Cubical.Foundations.Cubes.External

open import Agda.Builtin.List
open import Agda.Builtin.Reflection hiding (Type)
open import Cubical.Reflection.Base

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : A → Type ℓ'


-- Transform between external and internal cubes

private
  addImpl : ℕ → List (Arg Term) →  List (Arg Term)
  addImpl 0 t = t
  addImpl (suc n) t = harg {quantity-ω} unknown ∷ addImpl n t


-- The non-dependent cases

macro

  fromCube : (n : ℕ) → Term → Term → TC Unit
  fromCube 0 p t = unify p t
  fromCube (suc n) p t = unify t
    (def (quote Cube→ΠCubeᵉ) (addImpl 2 (ℕ→ℕᵉTerm (suc n) v∷ p v∷ [])))

  toCube : (n : ℕ) → Term → Term → TC Unit
  toCube 0 p t = unify p t
  toCube (suc n) p t = unify t
    (def (quote ΠCubeᵉ→Cube) (addImpl 2 (ℕ→ℕᵉTerm (suc n) v∷ p v∷ [])))

  from∂Cube : (n : ℕ) → Term → TC Unit
  from∂Cube 0 t = typeError
    (strErr "Only work for n>0." ∷ [])
  from∂Cube (suc n) t = unify t
    (def (quote ∂Cube→∂ΠCubeᵉ) (addImpl 2 (ℕ→ℕᵉTerm (suc n) v∷ [])))

  to∂Cube : (n : ℕ) → Term → TC Unit
  to∂Cube 0 t = typeError
    (strErr "Only work for n>0." ∷ [])
  to∂Cube (suc n) t = unify t
    (def (quote ∂ΠCubeᵉ→∂Cube) (addImpl 2 (ℕ→ℕᵉTerm (suc n) v∷ [])))


-- The dependent cases

macro

  fromCubeDep : (n : ℕ) → Term → Term → Term → Term → TC Unit
  fromCubeDep 0 B a b t = unify b t
  fromCubeDep (suc n) B a b t = unify t
    (def (quote CubeDep→ΠCubeDepᵉ) (addImpl 3 (ℕ→ℕᵉTerm (suc n) v∷ B v∷ a v∷ b v∷ [])))

  toCubeDep : (n : ℕ) → Term → Term → Term → Term → TC Unit
  toCubeDep 0 B a b t = unify b t
  toCubeDep (suc n) B a b t = unify t
    (def (quote ΠCubeDepᵉ→CubeDep) (addImpl 2 (ℕ→ℕᵉTerm (suc n) v∷ B v∷ a v∷ b v∷ [])))

  from∂CubeDep : (n : ℕ) → Term → TC Unit
  from∂CubeDep 0 t = typeError
    (strErr "Only work for n>0." ∷ [])
  from∂CubeDep (suc n) t = unify t
    (def (quote ∂CubeDep→∂ΠCubeDepᵉ) (addImpl 3 (ℕ→ℕᵉTerm (suc n) v∷ [])))

  to∂CubeDep : (n : ℕ) → Term → TC Unit
  to∂CubeDep 0 t = typeError
    (strErr "Only work for n>0." ∷ [])
  to∂CubeDep (suc n) t = unify t
    (def (quote ∂ΠCubeDepᵉ→∂CubeDep) (addImpl 3 (ℕ→ℕᵉTerm (suc n) v∷ [])))


-- To fill non-dependent cubes under h-level assumptions

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
    (def (quote fillCubeSuc) (addImpl 2 (ℕ→ℕᵉTerm n v∷ [])))


-- To fill dependent cubes under h-level assumptions

fillCubeDepSuc :
  (n : ℕᵉ) (h : isOfHLevelDep (ℕᵉ→ℕ (suc n)) B)
  (a : ΠCubeᵉ (suc n) A)
  (u : ΠCubeLiftᵉ (suc n) B a) → _
fillCubeDepSuc n h a u =
  CubeDepRel→ΠCubeLiftedᵉSuc n _ {a = ΠCubeᵉ→Cube (suc n) a} _
    (isOfHLevelDep→isCubeFilledDep (ℕᵉ→ℕ (suc n)) h (ΠCubeLiftᵉ→∂CubeDep (suc n) _ a u))

macro
  fillCubeDep : (n : ℕ) → Term → Term → TC Unit
  fillCubeDep 0 _ t = typeError
    (strErr "Only work for n>0." ∷ [])
  fillCubeDep (suc n) h t = unify t
    (def (quote fillCubeDepSuc) (addImpl 4 (ℕ→ℕᵉTerm n v∷ h v∷ [])))
