{-

Please do not move this file. Changes should only be made if
necessary.

This file contains benchmarks for the paper:

Synthetic Cohomology Theory in Cubical Agda


Command to run the benchmarks and get timings:

agda -v profile.definitions:10 Benchmarks.agda

This assumes that there is no Benchmarks.agdai file. If there is one,
then it should be removed before the above command is run.

-}

{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Experiments.ZCohomology.Benchmarks where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Int
open import Cubical.HITs.Sn
open import Cubical.Algebra.Group hiding (ℤ ; Bool)
open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Torus
open import Cubical.ZCohomology.Groups.KleinBottle
open import Cubical.ZCohomology.Groups.WedgeOfSpheres
open import Cubical.ZCohomology.Groups.RP2
open import Cubical.Data.Sigma

open import Cubical.HITs.KleinBottle
open import Cubical.HITs.RPn.Base

open IsGroupHom
open Iso

-- S¹ (everything fast)
module S1-tests where

  ϕ : coHom 1 (S₊ 1) → ℤ
  ϕ = fun (fst (Hⁿ-Sⁿ≅ℤ 0))

  ϕ⁻¹ : ℤ → coHom 1 (S₊ 1)
  ϕ⁻¹ = inv (fst (Hⁿ-Sⁿ≅ℤ 0))

  test₁ : ϕ (ϕ⁻¹ 0) ≡ 0    -- 30ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ 1) ≡ 1    -- <10ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 0) ≡ 0    -- <10ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 1) ≡ 1    -- 10ms
  test₄ = refl

  test₅ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 0) ≡ 1    -- 11ms
  test₅ = refl

  test₆ : ϕ (ϕ⁻¹ -3 +ₕ ϕ⁻¹ 4) ≡ 1    -- 29ms
  test₆ = refl

  test₇ : ϕ (ϕ⁻¹ -5 +ₕ ϕ⁻¹ -2) ≡ -7    -- 28ms
  test₇ = refl

-- S²
module S2-tests where

  ϕ : coHom 2 (S₊ 2) → ℤ
  ϕ = fun (fst (Hⁿ-Sⁿ≅ℤ 1))

  ϕ⁻¹ : ℤ → coHom 2 (S₊ 2)
  ϕ⁻¹ = inv (fst (Hⁿ-Sⁿ≅ℤ 1))

  test₁ : ϕ (ϕ⁻¹ 0) ≡ 0    -- 13ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ 1) ≡ 1    -- 16ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 0) ≡ 0    -- 278ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 1) ≡ 1    -- 290ms
  test₄ = refl

{-
  test₅ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 0) ≡ 1    -- nope
  test₅ = refl

  test₆ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 1) ≡ 2    -- nope
  test₆ = refl

  test₇ : ϕ (ϕ⁻¹ 2 +ₕ ϕ⁻¹ 4) ≡ 6    -- nope
  test₇ = refl
-}


module S1∨S1∨S2-tests₁ where -- everything fast

  ϕ : coHom 1 S²⋁S¹⋁S¹ → ℤ × ℤ
  ϕ = fun (fst H¹-S²⋁S¹⋁S¹)

  ϕ⁻¹ : ℤ × ℤ → coHom 1 S²⋁S¹⋁S¹
  ϕ⁻¹ = inv (fst H¹-S²⋁S¹⋁S¹)

  test₁ : ϕ (ϕ⁻¹ (0 , 0)) ≡ (0 , 0)    -- <10ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ (3 , 1)) ≡ (3 , 1)    -- 21ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ (0 , 0) +ₕ ϕ⁻¹ (0 , 0)) ≡ (0 , 0)    -- 15ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ (0 , 1) +ₕ ϕ⁻¹ (1 , 0)) ≡ (1 , 1)    -- 21ms
  test₄ = refl

  test₅ : ϕ (ϕ⁻¹ (3 , 2) +ₕ ϕ⁻¹ (-1 , 5)) ≡ (2 , 7)    -- 47ms
  test₅ = refl


module S1∨S1∨S2-tests₂ where

  ϕ : coHom 2 S²⋁S¹⋁S¹ → ℤ
  ϕ = fun (fst H²-S²⋁S¹⋁S¹)

  ϕ⁻¹ : ℤ → coHom 2 S²⋁S¹⋁S¹
  ϕ⁻¹ = inv (fst H²-S²⋁S¹⋁S¹)

  test₁ : ϕ (ϕ⁻¹ 0) ≡ 0    -- 157ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ 3) ≡ 3    -- 119ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 0) ≡ 0    -- 1,820ms
  test₃ = refl


module Torus-test₁ where -- fast

  ϕ : coHom 1 (S₊ 1 × S₊ 1) → ℤ × ℤ
  ϕ = fun (fst H¹-T²≅ℤ×ℤ)

  ϕ⁻¹ : ℤ × ℤ → coHom 1 (S₊ 1 × S₊ 1)
  ϕ⁻¹ = inv (fst H¹-T²≅ℤ×ℤ)

  test₁ : ϕ (ϕ⁻¹ (0 , 0)) ≡ (0 , 0)    -- <10ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ (3 , 1)) ≡ (3 , 1)    -- 18ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ (0 , 0) +ₕ ϕ⁻¹ (0 , 0)) ≡ (0 , 0)    -- 15ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ (0 , 1) +ₕ ϕ⁻¹ (1 , 0)) ≡ (1 , 1)    -- 20ms
  test₄ = refl

  test₅ : ϕ (ϕ⁻¹ (-3 , 2) +ₕ ϕ⁻¹ (-1 , 5)) ≡ (-4 , 7)    -- 44ms
  test₅ = refl


module Torus-test₂ where

  ϕ : coHom 2 (S₊ 1 × S₊ 1) → ℤ
  ϕ = fun (fst H²-T²≅ℤ)

  ϕ⁻¹ : ℤ → coHom 2 (S₊ 1 × S₊ 1)
  ϕ⁻¹ = inv (fst H²-T²≅ℤ)

  test₁ : ϕ (ϕ⁻¹ 0) ≡ 0    -- 121ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ 3) ≡ 3    -- 142ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 0) ≡ 0    -- 3,674ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 1) ≡ 1    -- 3,772ms
  test₄ = refl

{-
  test₅ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 0) ≡ 1    -- nope
  test₅ = refl
-}

module Klein-test₁ where -- fast

  ϕ : coHom 1 KleinBottle → ℤ
  ϕ = fun (fst H¹-𝕂²≅ℤ)

  ϕ⁻¹ : ℤ → coHom 1 KleinBottle
  ϕ⁻¹ = inv (fst H¹-𝕂²≅ℤ)

  test₁ : ϕ (ϕ⁻¹ 0) ≡ 0    -- <10ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ 3) ≡ 3    -- 12ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 0) ≡ 0    -- <10ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 1) ≡ 1    -- 11ms
  test₄ = refl

  test₅ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 0) ≡ 1    -- 12ms
  test₅ = refl

  test₆ : ϕ (ϕ⁻¹ -3 +ₕ ϕ⁻¹ 4) ≡ 1    -- 29ms
  test₆ = refl

  test₇ : ϕ (ϕ⁻¹ -5 +ₕ ϕ⁻¹ -2) ≡ -7    -- 29ms
  test₇ = refl

  -- The example in the paper:
  test : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 2) ≡ 3     -- 15ms
  test = refl


module Klein-test₂ where
  ϕ : coHom 2 KleinBottle → Bool
  ϕ = fun (fst H²-𝕂²≅Bool)

  ϕ⁻¹ : Bool → coHom 2 KleinBottle
  ϕ⁻¹ = inv (fst H²-𝕂²≅Bool)

{-
  test₀ : ϕ (0ₕ _) ≡ true -- fails already here...
  test₀ = refl
-}

module RP2-test₂ where
  ϕ : coHom 2 RP² → Bool
  ϕ = fun (fst H²-RP²≅Bool)

  ϕ⁻¹ : Bool → coHom 2 RP²
  ϕ⁻¹ = inv (fst H²-RP²≅Bool)

  test₀ : ϕ (0ₕ _) ≡ true    -- 1,210ms (unlike for Klein, this works)
  test₀ = refl

{-
  test₁ : ϕ (ϕ⁻¹ true) ≡ true    -- nope
  test₁ = refl
-}
