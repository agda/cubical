{-

The Internal n-Cubes

-}
module Cubical.Foundations.Cubes where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Cubes.Base public
open import Cubical.Foundations.Cubes.HLevels

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


{-

  Relation with the external (partial) cubes

-}

-- Concatenate two sides and parts in between to get a partial element.
concat :
  {φ : I} (a₋ : (i : I) → Partial φ A)
  (a₀ : A [ φ ↦ a₋ i0 ]) (a₁ : A [ φ ↦ a₋ i1 ])
  (i : I) → Partial (i ∨ ~ i ∨ φ) A
concat {φ = φ} a₋ a₀ a₁ i (i = i0) = outS a₀
concat {φ = φ} a₋ a₀ a₁ i (i = i1) = outS a₁
concat {φ = φ} a₋ a₀ a₁ i (φ = i1) = a₋ i 1=1

-- And the reverse procedure.
module _ (φ : I) (a₋ : (i : I) → Partial (i ∨ ~ i ∨ φ) A) where

  detach₀ : A
  detach₀ = a₋ i0 1=1

  detach₁ : A
  detach₁ = a₋ i1 1=1

  detach₋ : (i : I) → Partial φ A
  detach₋ i (φ = i1) = a₋ i 1=1


{- Lower Cubes Back and Forth -}

-- Notice that the functions are meta-inductively defined,
-- except for the first two cases when n = 0 or 1.

-- TODO : Write macros to generate them!!!

fromCube0 : Cube 0 A → A
fromCube0 p = p

fromCube1 : Cube 1 A → (i : I) → A
fromCube1 p i = p .snd i

fromCube2 : Cube 2 A → (i j : I) → A
fromCube2 p i j = p .snd i j

from3Cube : Cube 3 A → (i j k : I) → A
from3Cube p i j k = p .snd i j k

fromCube4 : Cube 4 A → (i j k l : I) → A
fromCube4 p i j k l = p .snd i j k l


toCube0 : A → Cube 0 A
toCube0 p = p

toCube1 : ((i : I) → A) → Cube 1 A
toCube1 p = (p i0 , p i1) , λ i → p i

toCube2 : ((i j : I) → A) → Cube 2 A
toCube2 p = pathCube 0 (λ i → (toCube1 (λ j → p i j)))

to3Cube : ((i j k : I) → A) → Cube 3 A
to3Cube p = pathCube 1 (λ i → (toCube2 (λ j → p i j)))

toCube4 : ((i j k l : I) → A) → Cube 4 A
toCube4 p = pathCube 2 (λ i → (to3Cube (λ j → p i j)))


-- The 0-cube has no (or empty) boundary...

from∂Cube1 : ∂Cube 1 A → (i : I) → Partial (i ∨ ~ i) A
from∂Cube1 (a , b) i = λ { (i = i0) → a ; (i = i1) → b }

from∂Cube2 : ∂Cube 2 A → (i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A
from∂Cube2 (a₀ , a₁ , ∂₋) i j =
  concat (λ t → from∂Cube1 (∂₋ t) j)
    (inS (fromCube1 a₀ j)) (inS (fromCube1 a₁ j)) i

from∂3Cube : ∂Cube 3 A → (i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k) A
from∂3Cube (a₀ , a₁ , ∂₋) i j k =
  concat (λ t → from∂Cube2 (∂₋ t) j k)
    (inS (fromCube2 a₀ j k)) (inS (fromCube2 a₁ j k)) i

from∂Cube4 : ∂Cube 4 A → (i j k l : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) A
from∂Cube4 (a₀ , a₁ , ∂₋) i j k l =
  concat (λ t → from∂3Cube (∂₋ t) j k l)
    (inS (from3Cube a₀ j k l)) (inS (from3Cube a₁ j k l)) i


to∂Cube1 : ((i : I) → Partial (i ∨ ~ i) A) → ∂Cube 1 A
to∂Cube1 p = p i0 1=1 , p i1 1=1

to∂Cube2 : ((i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A) → ∂Cube 2 A
to∂Cube2 p .fst      = toCube1 (λ j → detach₀ (j ∨ ~ j) (λ i → p i j))
to∂Cube2 p .snd .fst = toCube1 (λ j → detach₁ (j ∨ ~ j) (λ i → p i j))
to∂Cube2 p .snd .snd t = to∂Cube1 (λ j → detach₋ _ (λ i → p i j) t)

to∂3Cube : ((i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k) A) → ∂Cube 3 A
to∂3Cube p .fst      = toCube2 (λ j k → detach₀ (j ∨ ~ j ∨ k ∨ ~ k) (λ i → p i j k))
to∂3Cube p .snd .fst = toCube2 (λ j k → detach₁ (j ∨ ~ j ∨ k ∨ ~ k) (λ i → p i j k))
to∂3Cube p .snd .snd t = to∂Cube2 (λ j k → detach₋ _ (λ i → p i j k) t)

to∂Cube4 : ((i j k l : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) A) → ∂Cube 4 A
to∂Cube4 p .fst      = to3Cube (λ j k l → detach₀ (j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) (λ i → p i j k l))
to∂Cube4 p .snd .fst = to3Cube (λ j k l → detach₁ (j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) (λ i → p i j k l))
to∂Cube4 p .snd .snd t = to∂3Cube (λ j k l → detach₋ _ (λ i → p i j k l) t)


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

-- The property that, given an n-boundary, there always exists an n-cube extending this boundary
-- The case n=0 is not very meaningful, so we use `isContr` instead to keep its relation with h-levels.
-- It generalizes `isSet'` and `isGroupoid'`.

isCubeFilled : ℕ → Type ℓ → Type ℓ
isCubeFilled 0 = isContr
isCubeFilled (suc n) A = (∂ : ∂Cube (suc n) A) → CubeRel (suc n) A ∂

isCubeFilledDep : (n : ℕ) {A : Type ℓ} (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isCubeFilledDep 0 B = isOfHLevelDep 0 B
isCubeFilledDep (suc n) {A} B = {a₋ : Cube (suc n) A} (∂ : ∂CubeDep B (∂ a₋)) → CubeDepRel {n = suc n} a₋ ∂

-- We have the following logical equivalences between h-levels and cube-filling

isOfHLevel→isCubeFilled : (n : HLevel) → isOfHLevel n A → isCubeFilled n A
isOfHLevelDep→isCubeFilledDep : (n : HLevel) {B : A → Type ℓ'} → isOfHLevelDep n B → isCubeFilledDep n B

isCubeFilled→isOfHLevel : (n : HLevel) → isCubeFilled n A → isOfHLevel n A
isCubeFilledDep→isOfHLevelDep : (n : HLevel) {B : A → Type ℓ'} → isCubeFilledDep n B → isOfHLevelDep n B

Their proofs are put in `Cubical.Foundations.Cubes.HLevels`.

-}


-- Some special cases
-- TODO: Write a macro to generate them!!!

fillCube1 :
  (h : isOfHLevel 1 A)
  (u : (i : I) → Partial (i ∨ ~ i) A)
  (i : I) → A [ _ ↦ u i ]
fillCube1 h u i =
  inS (fromCube1 (to∂Cube1 u , isOfHLevel→isCubeFilled 1 h (to∂Cube1 u)) i)

fillCube2 :
  (h : isOfHLevel 2 A)
  (u : (i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A)
  (i j : I) → A [ _ ↦ u i j ]
fillCube2 h u i j =
  inS (fromCube2 (to∂Cube2 u , isOfHLevel→isCubeFilled 2 h (to∂Cube2 u)) i j)

fill3Cube :
  (h : isOfHLevel 3 A)
  (u : (i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k) A)
  (i j k : I) → A [ _ ↦ u i j k ]
fill3Cube h u i j k =
  inS (from3Cube (to∂3Cube u , isOfHLevel→isCubeFilled 3 h (to∂3Cube u)) i j k)

fillCube4 :
  (h : isOfHLevel 4 A)
  (u : (i j k l : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) A)
  (i j k l : I) → A [ _ ↦ u i j k l ]
fillCube4 h u i j k l =
  inS (fromCube4 (to∂Cube4 u , isOfHLevel→isCubeFilled 4 h (to∂Cube4 u)) i j k l)
