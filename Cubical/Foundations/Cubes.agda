{-

The Internal n-Cubes

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Cubes where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Cubes.Base public
open import Cubical.Data.Nat

private
  variable
    ℓ : Level
    A : Type ℓ


{-

By mutual recursion, one can define the type of

- n-Cubes:
  Cube    : (n : ℕ) (A : Type ℓ) → Type ℓ

- Boundary of n-cubes:
  ∂Cube   : (n : ℕ) (A : Type ℓ) → Type ℓ

- n-Cubes with Fixed Boundary:
  CubeRel : (n : ℕ) (A : Type ℓ) → ∂Cube n A → Type ℓ

Their definitions are put in `Cubical.Foundations.Cubes.Base`,
to avoid cyclic dependence.

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

from0Cube : Cube 0 A → A
from0Cube p = p

from1Cube : Cube 1 A → (i : I) → A
from1Cube p i = p .snd i

from2Cube : Cube 2 A → (i j : I) → A
from2Cube p i j = p .snd i j

from3Cube : Cube 3 A → (i j k : I) → A
from3Cube p i j k = p .snd i j k

from4Cube : Cube 4 A → (i j k l : I) → A
from4Cube p i j k l = p .snd i j k l


to0Cube : A → Cube 0 A
to0Cube p = p

to1Cube : ((i : I) → A) → Cube 1 A
to1Cube p = (p i0 , p i1) , λ i → p i

to2Cube : ((i j : I) → A) → Cube 2 A
to2Cube p = pathCube 0 (λ i → (to1Cube (λ j → p i j)))

to3Cube : ((i j k : I) → A) → Cube 3 A
to3Cube p = pathCube 1 (λ i → (to2Cube (λ j → p i j)))

to4Cube : ((i j k l : I) → A) → Cube 4 A
to4Cube p = pathCube 2 (λ i → (to3Cube (λ j → p i j)))


-- The 0-cube has no (or empty) boundary...

from∂1Cube : ∂Cube 1 A → (i : I) → Partial (i ∨ ~ i) A
from∂1Cube (a , b) i = λ { (i = i0) → a ; (i = i1) → b }

from∂2Cube : ∂Cube 2 A → (i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A
from∂2Cube (a₀ , a₁ , ∂₋) i j =
  concat (λ t → from∂1Cube (∂₋ t) j)
    (inS (from1Cube a₀ j)) (inS (from1Cube a₁ j)) i

from∂3Cube : ∂Cube 3 A → (i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k) A
from∂3Cube (a₀ , a₁ , ∂₋) i j k =
  concat (λ t → from∂2Cube (∂₋ t) j k)
    (inS (from2Cube a₀ j k)) (inS (from2Cube a₁ j k)) i

from∂4Cube : ∂Cube 4 A → (i j k l : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) A
from∂4Cube (a₀ , a₁ , ∂₋) i j k l =
  concat (λ t → from∂3Cube (∂₋ t) j k l)
    (inS (from3Cube a₀ j k l)) (inS (from3Cube a₁ j k l)) i


to∂1Cube : ((i : I) → Partial (i ∨ ~ i) A) → ∂Cube 1 A
to∂1Cube p = p i0 1=1 , p i1 1=1

to∂2Cube : ((i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A) → ∂Cube 2 A
to∂2Cube p .fst      = to1Cube (λ j → detach₀ (j ∨ ~ j) (λ i → p i j))
to∂2Cube p .snd .fst = to1Cube (λ j → detach₁ (j ∨ ~ j) (λ i → p i j))
to∂2Cube p .snd .snd t = to∂1Cube (λ j → detach₋ _ (λ i → p i j) t)

to∂3Cube : ((i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k) A) → ∂Cube 3 A
to∂3Cube p .fst      = to2Cube (λ j k → detach₀ (j ∨ ~ j ∨ k ∨ ~ k) (λ i → p i j k))
to∂3Cube p .snd .fst = to2Cube (λ j k → detach₁ (j ∨ ~ j ∨ k ∨ ~ k) (λ i → p i j k))
to∂3Cube p .snd .snd t = to∂2Cube (λ j k → detach₋ _ (λ i → p i j k) t)

to∂4Cube : ((i j k l : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) A) → ∂Cube 4 A
to∂4Cube p .fst      = to3Cube (λ j k l → detach₀ (j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) (λ i → p i j k l))
to∂4Cube p .snd .fst = to3Cube (λ j k l → detach₁ (j ∨ ~ j ∨ k ∨ ~ k ∨ l ∨ ~ l) (λ i → p i j k l))
to∂4Cube p .snd .snd t = to∂3Cube (λ j k l → detach₋ _ (λ i → p i j k l) t)


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
  sec-∂2Cube p i j = λ
    { (i = i0) → refl ; (i = i1) → refl ; (j = i0) → refl ; (j = i1) → refl }


{-

  The n-cubes-can-always-be-filled is equivalent to be of h-level n

-}

-- The property that, given an n-boundary, there always exists an n-cube extending this boundary
-- The case n=0 is not very meaningful, so we use `isContr` instead to keep its relation with h-levels.

isCubeFilled : ℕ → Type ℓ → Type ℓ
isCubeFilled 0 = isContr
isCubeFilled (suc n) A = (∂ : ∂Cube (suc n) A) → CubeRel (suc n) A ∂


{-

TODO:

-- It's not too difficult to show this for a specific n,
-- the trickiest part is to make it for all n.

isOfHLevel→isCubeFilled : (n : HLevel) → isOfHLevel n A → isCubeFilled n A

isCubeFilled→isOfHLevel : (n : HLevel) → isCubeFilled n A → isOfHLevel n A

-}
