{-

The Cube-Filling Characterization of hLevels

-}
module Cubical.Foundations.Cubes.HLevels where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Cubes.Base
open import Cubical.Foundations.Cubes.Subtypes
open import Cubical.Foundations.Cubes.Dependent

open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma.Properties

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : A → Type ℓ'


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

isCubeFilledPath≡Suc : (n : ℕ) (A : Type ℓ)
  → isCubeFilledPath (suc n) A ≡ isCubeFilled (suc (suc n)) A
isCubeFilledPath≡Suc n A =
    (λ i → (x y : A)(∂ : ∂CubeConst₀₁≡∂CubePath {n = suc n} {a₀ = x} {y} (~ i))
        → CubeRelConst₀₁≡CubeRelPath (~ i) ∂)
  ∙ (λ i → (x : A) → isoToPath (curryIso {A = A}
      {B = λ y → ∂CubeConst₀₁ (suc n) A x y} {C = λ _ ∂ → CubeRelConst₀₁ (suc n) A ∂}) (~ i))
  ∙ sym (isoToPath curryIso)
  ∙ (λ i → (∂ : ∂CubeConst₀₁≡∂CubeSuc {A = A} i) → CubeRelConst₀₁≡CubeRelSuc {n = n} i ∂)

isCubeFilledPath→Suc : (n : ℕ) (A : Type ℓ)
  → isCubeFilledPath n A → isCubeFilled (suc n) A
isCubeFilledPath→Suc 0 A h (x , y) = h x y .fst
isCubeFilledPath→Suc (suc n) A = transport (isCubeFilledPath≡Suc n A)

isCubeFilledSuc→Path : (n : ℕ) (A : Type ℓ)
  → isCubeFilled (suc n) A → isCubeFilledPath n A
isCubeFilledSuc→Path 0 A h = isProp→isContrPath (λ x y → h (x , y))
isCubeFilledSuc→Path (suc n) A = transport (sym (isCubeFilledPath≡Suc n A))


-- The characterization of h-levels by cube-filling

isOfHLevel→isCubeFilled : (n : HLevel) → isOfHLevel n A → isCubeFilled n A
isOfHLevel→isCubeFilled 0 h = h
isOfHLevel→isCubeFilled (suc n) h = isCubeFilledPath→Suc _ _
  (λ x y → isOfHLevel→isCubeFilled _ (isOfHLevelPath' _ h x y))

isCubeFilled→isOfHLevel : (n : HLevel) → isCubeFilled n A → isOfHLevel n A
isCubeFilled→isOfHLevel 0 h = h
isCubeFilled→isOfHLevel (suc n) h = isOfHLevelPath'⁻ _
  (λ x y → isCubeFilled→isOfHLevel _ (isCubeFilledSuc→Path _ _ h x y))


{-

  The dependent-n-cubes-can-always-be-filled is equivalent to be of dependent h-level n

-}


-- Dependent cube filling

isCubeFilledDep : (n : ℕ) {A : Type ℓ} (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isCubeFilledDep 0 B = isOfHLevelDep 0 B
isCubeFilledDep (suc n) {A} B = {a₋ : Cube (suc n) A} (∂ : ∂CubeDep B (∂ a₋)) → CubeDepRel {n = suc n} a₋ ∂


-- Some preliminary lemmas

isCubeFilledDepConst : (n : ℕ) (B : A → Type ℓ') (a : A) → Type ℓ'
isCubeFilledDepConst 0 B a = isContr (B a)
isCubeFilledDepConst (suc n) B a = (∂ : ∂CubeDepConst (suc n) B a) → CubeDepConstRel ∂


isCubeFilledDepConst≡Fiber : (n : ℕ) (B : A → Type ℓ') (a : A)
  → isCubeFilledDepConst n B a ≡ isCubeFilled n (B a)
isCubeFilledDepConst≡Fiber 0 B a = refl
isCubeFilledDepConst≡Fiber (suc n) B a i =
  (∂ : ∂CubeDepConst≡∂Cube (suc n) B a i) → (CubeDepConstRel≡CubeRel (suc n) B a i ∂)

isCubeFilledDepConst→Fiber : (n : ℕ) (B : A → Type ℓ') (a : A)
  → isCubeFilledDepConst n B a → isCubeFilled n (B a)
isCubeFilledDepConst→Fiber _ _ _ =
  transport (isCubeFilledDepConst≡Fiber _ _ _)

isCubeFilledFiber→DepConst : (n : ℕ) (B : A → Type ℓ') (a : A)
  → isCubeFilled n (B a) → isCubeFilledDepConst n B a
isCubeFilledFiber→DepConst _ _ _ =
  transport (sym (isCubeFilledDepConst≡Fiber _ _ _))


-- The dependent cube-filling characterization of dependent h-levels

isOfHLevelDep→isCubeFilledDep : (n : HLevel) {B : A → Type ℓ'} → isOfHLevelDep n B → isCubeFilledDep n B
isOfHLevelDep→isCubeFilledDep 0 {B} h = h
isOfHLevelDep→isCubeFilledDep {A = A} (suc n) {B} h =
  JCube (λ a₋ → (∂b : ∂CubeDep B (∂ a₋)) → CubeDepRel {n = suc n} a₋ ∂b) d _
  where
  d : _
  d a = isCubeFilledFiber→DepConst _ B a
    (isOfHLevel→isCubeFilled _ (isOfHLevelDep→isOfHLevel _ h a))

isCubeFilledDep→isOfHLevelDep : (n : HLevel) {B : A → Type ℓ'} → isCubeFilledDep n B → isOfHLevelDep n B
isCubeFilledDep→isOfHLevelDep 0 {B} h = h
isCubeFilledDep→isOfHLevelDep {A = A} (suc n) {B} h =
  isOfHLevel→isOfHLevelDep _ (λ a →
    isCubeFilled→isOfHLevel _ (isCubeFilledDepConst→Fiber _ B a h))
