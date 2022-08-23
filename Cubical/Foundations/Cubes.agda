{-

The Internal n-Cubes

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Cubes where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Cubes.Base public
open import Cubical.Foundations.Cubes.External
open import Cubical.Foundations.Cubes.Subtypes

open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma.Properties

open import Agda.Builtin.List
open import Agda.Builtin.Reflection hiding (Type)
open import Cubical.Reflection.Base

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

-}


{- Lower Cubes Back and Forth -}

-- Notice that the functions are meta-inductively defined,
-- except for the first two cases when n = 0 or 1.

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


-- Special cases of low dimension

from0Cube : Cube 0 A → A
from0Cube p = fromCube 0 p

from1Cube : Cube 1 A → (i : I) → A
from1Cube p = fromCube 1 p

from2Cube : Cube 2 A → (i j : I) → A
from2Cube p = fromCube 2 p

from3Cube : Cube 3 A → (i j k : I) → A
from3Cube p = fromCube 3 p

from4Cube : Cube 4 A → (i j k l : I) → A
from4Cube p = fromCube 4 p


to0Cube : A → Cube 0 A
to0Cube p = toCube 0 p

to1Cube : ((i : I) → A) → Cube 1 A
to1Cube p = toCube 1 p

to2Cube : ((i j : I) → A) → Cube 2 A
to2Cube p = toCube 2 p

to3Cube : ((i j k : I) → A) → Cube 3 A
to3Cube p = toCube 3 p

to4Cube : ((i j k l : I) → A) → Cube 4 A
to4Cube p = toCube 4 p


-- The 0-cube has no (or empty) boundary...

from∂1Cube : ∂Cube 1 A → (i : I) → Partial (i ∨ ~ i) A
from∂1Cube p = from∂Cube 1 p

from∂2Cube : ∂Cube 2 A → (i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A
from∂2Cube p = from∂Cube 2 p

from∂3Cube : ∂Cube 3 A → (i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k) A
from∂3Cube p = from∂Cube 3 p

from∂4Cube : ∂Cube 4 A → (i j k l : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) A
from∂4Cube p = from∂Cube 4 p


to∂1Cube : ((i : I) → Partial (i ∨ ~ i) A) → ∂Cube 1 A
to∂1Cube p = to∂Cube 1 p

to∂2Cube : ((i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A) → ∂Cube 2 A
to∂2Cube p = to∂Cube 2 p

to∂3Cube : ((i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k) A) → ∂Cube 3 A
to∂3Cube p = to∂Cube 3 p

to∂4Cube : ((i j k l : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) A) → ∂Cube 4 A
to∂4Cube p = to∂Cube 4 p


-- They're strict isomorphisms actually.
-- The following is an example.

private

  ret-2Cube : {A : Type ℓ} (a : Cube 2 A) → to2Cube (from2Cube a) ≡ a
  ret-2Cube a = refl

  sec-2Cube : (p : (i j : I) → A) → (i j : I) → from2Cube (to2Cube p) i j ≡ p i j
  sec-2Cube p i j = refl

  ret-∂2Cube : {A : Type ℓ} (a : ∂Cube 2 A) → to∂2Cube (from∂2Cube a) ≡ a
  ret-∂2Cube a = refl

  sec-∂2Cube : (p : (i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A)
    → (i j : I) → PartialP (i ∨ ~ i ∨ j ∨ ~ j) (λ o → from∂2Cube (to∂2Cube p) i j o ≡ p i j o)
  sec-∂2Cube p i j = λ { (i = i0) → refl ; (i = i1) → refl ; (j = i0) → refl ; (j = i1) → refl }


{-

  The n-cubes-can-always-be-filled is equivalent to be of h-level n

-}


-- The property that, given an n-boundary, there always exists an n-cube extending this boundary
-- The case n=0 is not very meaningful, so we use `isContr` instead to keep its relation with h-levels.
-- It generalizes `isSet'` and `isGroupoid'`.

isCubeFilled : ℕ → Type ℓ → Type ℓ
isCubeFilled 0 = isContr
isCubeFilled (suc n) A = (∂ : ∂Cube (suc n) A) → CubeRel (suc n) A ∂


-- Some preliminary results to relate cube-filling to h-levels.

isCubeFilledPath : ℕ → Type ℓ → Type ℓ
isCubeFilledPath n A = (x y : A) → isCubeFilled n (x ≡ y)

isCubeFilledPath≡isCubeFilledSuc : (n : ℕ) (A : Type ℓ)
  → isCubeFilledPath (suc n) A ≡ isCubeFilled (suc (suc n)) A
isCubeFilledPath≡isCubeFilledSuc n A =
    (λ i → (x y : A)(∂ : ∂Cube₀₁≡∂CubePath {n = suc n} {a₀ = x} {y} (~ i))
        → CubeRel₀₁≡CubeRelPath (~ i) ∂)
  ∙ (λ i → (x : A) → isoToPath (curryIso {A = A}
      {B = λ y → ∂Cube₀₁ (suc n) A x y} {C = λ _ ∂ → CubeRel₀₁ (suc n) A ∂}) (~ i))
  ∙ sym (isoToPath curryIso)
  ∙ (λ i → (∂ : ∂CubeConst₀₁≡∂Cube {n = suc n} {A} i) → CubeRelConst₀₁≡CubeRel₀₁ {n = suc n} i ∂)

isCubeFilledPath→isCubeFilledSuc : (n : ℕ) (A : Type ℓ)
  → isCubeFilledPath n A → isCubeFilled (suc n) A
isCubeFilledPath→isCubeFilledSuc 0 A h (x , y) = h x y .fst
isCubeFilledPath→isCubeFilledSuc (suc n) A = transport (isCubeFilledPath≡isCubeFilledSuc n A)

isCubeFilledSuc→isCubeFilledPath : (n : ℕ) (A : Type ℓ)
  → isCubeFilled (suc n) A → isCubeFilledPath n A
isCubeFilledSuc→isCubeFilledPath 0 A h = isProp→isContrPath (λ x y → h (x , y))
isCubeFilledSuc→isCubeFilledPath (suc n) A = transport (sym (isCubeFilledPath≡isCubeFilledSuc n A))


-- The characterization of h-levels by cube-filling

isOfHLevel→isCubeFilled : (n : HLevel) → isOfHLevel n A → isCubeFilled n A
isOfHLevel→isCubeFilled 0 h = h
isOfHLevel→isCubeFilled (suc n) h = isCubeFilledPath→isCubeFilledSuc _ _
  (λ x y → isOfHLevel→isCubeFilled n (isOfHLevelPath' n h x y))

isCubeFilled→isOfHLevel : (n : HLevel) → isCubeFilled n A → isOfHLevel n A
isCubeFilled→isOfHLevel 0 h = h
isCubeFilled→isOfHLevel (suc n) h = isOfHLevelPath'⁻ _
  (λ x y → isCubeFilled→isOfHLevel _ (isCubeFilledSuc→isCubeFilledPath _ _ h x y))


-- Some special cases

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


fill1Cube :
  (h : isOfHLevel 1 A)
  (u : (i : I) → Partial (i ∨ ~ i) A)
  (i : I) → A [ _ ↦ u i ]
fill1Cube h u = fillCube 1 h u

fill2Cube :
  (h : isOfHLevel 2 A)
  (u : (i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A)
  (i j : I) → A [ _ ↦ u i j ]
fill2Cube h u = fillCube 2 h u

fill3Cube :
  (h : isOfHLevel 3 A)
  (u : (i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k) A)
  (i j k : I) → A [ _ ↦ u i j k ]
fill3Cube h u = fillCube 3 h u

fill4Cube :
  (h : isOfHLevel 4 A)
  (u : (i j k l : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) A)
  (i j k l : I) → A [ _ ↦ u i j k l ]
fill4Cube h u = fillCube 4 h u
