{-

The Cube-Filling Characterization of hLevels

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Cubes.HLevels where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Cubes.Base
open import Cubical.Foundations.Cubes.Subtypes

open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma.Properties

private
  variable
    ℓ : Level
    A : Type ℓ


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
