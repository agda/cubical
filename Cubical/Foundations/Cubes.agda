{-

The Internal n-Cubes

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Cubes where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Cubes.Base public
open import Cubical.Foundations.Cubes.HLevels
open import Cubical.Foundations.Cubes.Macros

private
  variable
    ℓ : Level
    A : Type ℓ


{-

By mutual recursion, one can define the type of

- n-Cubes:
  Cube    : (n : ℕ) (A : Type ℓ) → Type ℓ

- Boundary of n-Cubes:
  ∂Cube   : (n : ℕ) (A : Type ℓ) → Type ℓ

- n-Cubes with Specified Boundary:
  CubeRel : (n : ℕ) (A : Type ℓ) → ∂Cube n A → Type ℓ

Their definitions are put in `Cubical.Foundations.Cubes.Base`,
to avoid cyclic dependence.

They also have dependent versions,
of which definitions and properties are given in `Cubical.Foundations.Cubes.Dependent`.

CubeDep    : {A : Type ℓ} (B : A → Type ℓ') →  Cube n A → Type ℓ'
∂CubeDep   : {A : Type ℓ} (B : A → Type ℓ') → ∂Cube n A → Type ℓ'
CubeDepRel : {A : Type ℓ} {B : A → Type ℓ'} (a₋ : Cube n A) → ∂CubeDep {n = n} B (∂ a₋) → Type ℓ'

-}


{- Lower Cubes Back and Forth -}

fromCube0 : Cube 0 A → A
fromCube0 p = fromCube 0 p

fromCube1 : Cube 1 A → (i : I) → A
fromCube1 p = fromCube 1 p

fromCube2 : Cube 2 A → (i j : I) → A
fromCube2 p = fromCube 2 p

from3Cube : Cube 3 A → (i j k : I) → A
from3Cube p = fromCube 3 p

fromCube4 : Cube 4 A → (i j k l : I) → A
fromCube4 p = fromCube 4 p


toCube0 : A → Cube 0 A
toCube0 p = toCube 0 p

toCube1 : ((i : I) → A) → Cube 1 A
toCube1 p = toCube 1 p

toCube2 : ((i j : I) → A) → Cube 2 A
toCube2 p = toCube 2 p

to3Cube : ((i j k : I) → A) → Cube 3 A
to3Cube p = toCube 3 p

toCube4 : ((i j k l : I) → A) → Cube 4 A
toCube4 p = toCube 4 p


-- The 0-cube has no (or empty) boundary...

from∂Cube1 : ∂Cube 1 A → (i : I) → Partial (i ∨ ~ i) A
from∂Cube1 p = from∂Cube 1 p

from∂Cube2 : ∂Cube 2 A → (i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A
from∂Cube2 p = from∂Cube 2 p

from∂3Cube : ∂Cube 3 A → (i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k) A
from∂3Cube p = from∂Cube 3 p

from∂Cube4 : ∂Cube 4 A → (i j k l : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) A
from∂Cube4 p = from∂Cube 4 p


to∂Cube1 : ((i : I) → Partial (i ∨ ~ i) A) → ∂Cube 1 A
to∂Cube1 p = to∂Cube 1 p

to∂Cube2 : ((i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A) → ∂Cube 2 A
to∂Cube2 p = to∂Cube 2 p

to∂3Cube : ((i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k) A) → ∂Cube 3 A
to∂3Cube p = to∂Cube 3 p

to∂Cube4 : ((i j k l : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) A) → ∂Cube 4 A
to∂Cube4 p = to∂Cube 4 p


-- They're strict isomorphisms actually.
-- The following is an example.

private

  ret-Cube2 : {A : Type ℓ} (a : Cube 2 A) → toCube2 (fromCube2 a) ≡ a
  ret-Cube2 a = refl

  sec-Cube2 : (p : (i j : I) → A) → (i j : I) → fromCube2 (toCube2 p) i j ≡ p i j
  sec-Cube2 p i j = refl

  ret-∂Cube2 : {A : Type ℓ} (a : ∂Cube 2 A) → to∂Cube2 (from∂Cube2 a) ≡ a
  ret-∂Cube2 a = refl

  sec-∂Cube2 : (p : (i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A)
    → (i j : I) → PartialP (i ∨ ~ i ∨ j ∨ ~ j) (λ o → from∂Cube2 (to∂Cube2 p) i j o ≡ p i j o)
  sec-∂Cube2 p i j = λ
    { (i = i0) → refl ; (i = i1) → refl ; (j = i0) → refl ; (j = i1) → refl }


{-

  The n-cubes-can-always-be-filled is equivalent to be of h-level n

-}


{-

The property that, given an n-boundary, there always exists an n-cube extending this boundary:

isCubeFilled : ℕ → Type ℓ → Type ℓ
isCubeFilled 0 = isContr
isCubeFilled (suc n) A = (∂ : ∂Cube (suc n) A) → CubeRel (suc n) A ∂

isCubeFilledDep : (n : ℕ) {A : Type ℓ} (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isCubeFilledDep 0 B = isOfHLevelDep 0 B
isCubeFilledDep (suc n) {A} B = {a₋ : Cube (suc n) A} (∂ : ∂CubeDep B (∂ a₋)) → CubeDepRel {n = suc n} a₋ ∂

The case n=0 is not very meaningful, so we use `isContr` instead to keep its relation with h-levels.
It generalizes `isSet'` and `isGroupoid'`.

We have the following logical equivalences between h-levels and cube-filling:

isOfHLevel→isCubeFilled : (n : HLevel) → isOfHLevel n A → isCubeFilled n A
isOfHLevelDep→isCubeFilledDep : (n : HLevel) {B : A → Type ℓ'} → isOfHLevelDep n B → isCubeFilledDep n B

isCubeFilled→isOfHLevel : (n : HLevel) → isCubeFilled n A → isOfHLevel n A
isCubeFilledDep→isOfHLevelDep : (n : HLevel) {B : A → Type ℓ'} → isCubeFilledDep n B → isOfHLevelDep n B

Their proofs are put in `Cubical.Foundations.Cubes.HLevels`.

-}


-- Lower-dimensional special cases

fillCube1 :
  (h : isOfHLevel 1 A)
  (u : (i : I) → Partial (i ∨ ~ i) A)
  (i : I) → A [ _ ↦ u i ]
fillCube1 h u = fillCube 1 h u

fillCube2 :
  (h : isOfHLevel 2 A)
  (u : (i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A)
  (i j : I) → A [ _ ↦ u i j ]
fillCube2 h u = fillCube 2 h u

fillCube3 :
  (h : isOfHLevel 3 A)
  (u : (i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k) A)
  (i j k : I) → A [ _ ↦ u i j k ]
fillCube3 h u = fillCube 3 h u

fillCube4 :
  (h : isOfHLevel 4 A)
  (u : (i j k l : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) A)
  (i j k l : I) → A [ _ ↦ u i j k l ]
fillCube4 h u = fillCube 4 h u
