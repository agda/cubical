{-

Please do not move this file. Changes should only be made if
necessary.

This file contains benchmarks for the paper:

Synthetic Integral Cohomology in Cubical Agda
Guillaume Brunerie, Axel Ljungström, Anders Mörtberg
Computer Science Logic (CSL) 2022

Command to run the benchmarks and get timings:

agda -v profile.definitions:10 Benchmarks.agda

This assumes that there is no Benchmarks.agdai file. If there is one,
then it should be removed before the above command is run.

-}

{-# OPTIONS --safe #-}
module Cubical.Experiments.ZCohomology.Benchmarks where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Int
open import Cubical.Data.Sigma

open import Cubical.HITs.Sn
open import Cubical.HITs.KleinBottle
open import Cubical.HITs.RPn.Base
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Pushout
open import Cubical.Homotopy.Hopf
open S¹Hopf
open import Cubical.HITs.Truncation
open import Cubical.HITs.Susp
open import Cubical.HITs.S1

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure hiding (_+ₕ_) renaming (_+'ₕ_ to _+ₕ_)
{- _+'ₕ_ is just (λ x y → (x +ₕ 0ₕ) +ₕ (y +ₕ 0ₕ))
   For technical reason, this gives nicer reductions and computes better in
   higher dimensions. -}
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Torus
open import Cubical.ZCohomology.Groups.KleinBottle
open import Cubical.ZCohomology.Groups.S2wedgeS1wedgeS1
open import Cubical.ZCohomology.Groups.RP2
open import Cubical.ZCohomology.Groups.CP2

open IsGroupHom
open Iso

-- S¹ (everything fast)
module S1-tests where

  ϕ : coHom 1 (S₊ 1) → ℤ
  ϕ = fun (fst (Hⁿ-Sⁿ≅ℤ 0))

  ϕ⁻¹ : ℤ → coHom 1 (S₊ 1)
  ϕ⁻¹ = inv (fst (Hⁿ-Sⁿ≅ℤ 0))

  test₁ : ϕ (ϕ⁻¹ 0) ≡ 0    -- <10ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ 1) ≡ 1    -- <10ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 0) ≡ 0   -- <10ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 1) ≡ 1    -- 12ms
  test₄ = refl

  test₅ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 0) ≡ 1    -- 13ms
  test₅ = refl

  test₆ : ϕ (ϕ⁻¹ -3 +ₕ ϕ⁻¹ 4) ≡ 1    -- 37ms
  test₆ = refl

  test₇ : ϕ (ϕ⁻¹ -5 +ₕ ϕ⁻¹ -2) ≡ -7    -- 38ms
  test₇ = refl

-- S²
module S2-tests where

  ϕ : coHom 2 (S₊ 2) → ℤ
  ϕ = fun (fst (Hⁿ-Sⁿ≅ℤ 1))

  ϕ⁻¹ : ℤ → coHom 2 (S₊ 2)
  ϕ⁻¹ = inv (fst (Hⁿ-Sⁿ≅ℤ 1))

  test₁ : ϕ (ϕ⁻¹ 0) ≡ 0    -- 13ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ 1) ≡ 1    -- 17ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 0) ≡ 0    -- 1,152ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 1) ≡ 1    -- 1,235ms
  test₄ = refl

  test₅ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 0) ≡ 1    -- 1,208ms
  test₅ = refl

  test₆ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 1) ≡ 2    -- 1,153ms
  test₆ = refl

  test₇ : ϕ (ϕ⁻¹ 2 +ₕ ϕ⁻¹ 4) ≡ 6    -- 1,365ms
  test₇ = refl

-- S³
module S3-tests where

  ϕ : coHom 3 (S₊ 3) → ℤ
  ϕ = fun (fst (Hⁿ-Sⁿ≅ℤ 2))

  ϕ⁻¹ : ℤ → coHom 3 (S₊ 3)
  ϕ⁻¹ = inv (fst (Hⁿ-Sⁿ≅ℤ 2))

  test₁ : ϕ (ϕ⁻¹ 0) ≡ 0    -- 228ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ 1) ≡ 1    -- 231ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ 3) ≡ 3    -- 325ms
  test₃ = refl

{-
  test₄ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 0) ≡ 0    -- nope
  test₄ = refl

  test₅ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 1) ≡ 1    -- nope
  test₅ = refl
-}

-- S⁴
module S4-tests where

  ϕ : coHom 4 (S₊ 4) → ℤ
  ϕ = fun (fst (Hⁿ-Sⁿ≅ℤ 3))

  ϕ⁻¹ : ℤ → coHom 4 (S₊ 4)
  ϕ⁻¹ = inv (fst (Hⁿ-Sⁿ≅ℤ 3))

{- _+ₕ_ Fails already here...
  test₁ : ϕ (ϕ⁻¹ 0) ≡ 0    -- nope
  test₁ = refl
-}

-- ϕ can handle 0ₕ fast
  test₂ : ϕ (0ₕ _) ≡ 0     -- < 10ms
  test₂ = refl

{- It fails to map the generator to 1, however.
  test₂ : ϕ (∣ ∣_∣ ∣₂) ≡ 1    -- nope
  test₂ = refl
-}

module S1∨S1∨S2-tests₁ where -- everything fast

  ϕ : coHom 1 S²⋁S¹⋁S¹ → ℤ × ℤ
  ϕ = fun (fst H¹-S²⋁S¹⋁S¹)

  ϕ⁻¹ : ℤ × ℤ → coHom 1 S²⋁S¹⋁S¹
  ϕ⁻¹ = inv (fst H¹-S²⋁S¹⋁S¹)

  test₁ : ϕ (ϕ⁻¹ (0 , 0)) ≡ (0 , 0)    -- 11ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ (3 , 1)) ≡ (3 , 1)    -- 23ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ (0 , 0) +ₕ ϕ⁻¹ (0 , 0)) ≡ (0 , 0)    -- 19ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ (0 , 1) +ₕ ϕ⁻¹ (1 , 0)) ≡ (1 , 1)    -- 26ms
  test₄ = refl

  test₅ : ϕ (ϕ⁻¹ (3 , 2) +ₕ ϕ⁻¹ (-1 , 5)) ≡ (2 , 7)    -- 62ms
  test₅ = refl


module S1∨S1∨S2-tests₂ where

  ϕ : coHom 2 S²⋁S¹⋁S¹ → ℤ
  ϕ = fun (fst H²-S²⋁S¹⋁S¹)

  ϕ⁻¹ : ℤ → coHom 2 S²⋁S¹⋁S¹
  ϕ⁻¹ = inv (fst H²-S²⋁S¹⋁S¹)

  test₁ : ϕ (ϕ⁻¹ 0) ≡ 0    -- 106ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ 3) ≡ 3    -- 125ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 0) ≡ 0    -- 9,689ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 1) ≡ 1    -- 9,235ms
  test₄ = refl

  test₅ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 0) ≡ 1    -- 9,748ms
  test₅ = refl

  test₆ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 1) ≡ 2    -- 9,136ms
  test₆ = refl

  test₇ : ϕ (ϕ⁻¹ 2 +ₕ ϕ⁻¹ 4) ≡ 6    -- 9,557ms
  test₇ = refl


module Torus-test₁ where -- fast

  ϕ : coHom 1 (S₊ 1 × S₊ 1) → ℤ × ℤ
  ϕ = fun (fst H¹-T²≅ℤ×ℤ)

  ϕ⁻¹ : ℤ × ℤ → coHom 1 (S₊ 1 × S₊ 1)
  ϕ⁻¹ = inv (fst H¹-T²≅ℤ×ℤ)

  test₁ : ϕ (ϕ⁻¹ (0 , 0)) ≡ (0 , 0)    -- 11ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ (3 , 1)) ≡ (3 , 1)    -- 17ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ (0 , 0) +ₕ ϕ⁻¹ (0 , 0)) ≡ (0 , 0)    -- 19ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ (0 , 1) +ₕ ϕ⁻¹ (1 , 0)) ≡ (1 , 1)    -- 26ms
  test₄ = refl

  test₅ : ϕ (ϕ⁻¹ (-3 , 2) +ₕ ϕ⁻¹ (-1 , 5)) ≡ (-4 , 7)    -- 61ms
  test₅ = refl


module Torus-test₂ where

  ϕ : coHom 2 (S₊ 1 × S₊ 1) → ℤ
  ϕ = fun (fst H²-T²≅ℤ)

  ϕ⁻¹ : ℤ → coHom 2 (S₊ 1 × S₊ 1)
  ϕ⁻¹ = inv (fst H²-T²≅ℤ)

  test₁ : ϕ (ϕ⁻¹ 0) ≡ 0    -- 136sm
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ 3) ≡ 3    -- 154ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 0) ≡ 0    -- 12,790ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 1) ≡ 1    -- 12,366ms
  test₄ = refl

  test₅ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 0) ≡ 1    -- 12,257ms
  test₅ = refl

  test₆ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 1) ≡ 2    -- 13,092ms
  test₆ = refl

  test₇ : ϕ (ϕ⁻¹ 2 +ₕ ϕ⁻¹ 4) ≡ 6    -- 12,528ms
  test₇ = refl


module Klein-test₁ where -- fast

  ϕ : coHom 1 KleinBottle → ℤ
  ϕ = fun (fst H¹-𝕂²≅ℤ)

  ϕ⁻¹ : ℤ → coHom 1 KleinBottle
  ϕ⁻¹ = inv (fst H¹-𝕂²≅ℤ)

  test₁ : ϕ (ϕ⁻¹ 0) ≡ 0    -- <10ms
  test₁ = refl

  test₂ : ϕ (ϕ⁻¹ 3) ≡ 3    -- 13ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 0) ≡ 0    -- 10ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 1) ≡ 1    -- 14ms
  test₄ = refl

  test₅ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 0) ≡ 1    -- 14ms
  test₅ = refl

  test₆ : ϕ (ϕ⁻¹ -3 +ₕ ϕ⁻¹ 4) ≡ 1    -- 38ms
  test₆ = refl

  test₇ : ϕ (ϕ⁻¹ -5 +ₕ ϕ⁻¹ -2) ≡ -7    -- 38ms
  test₇ = refl

  -- The example in the paper:
  test : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 2) ≡ 3     -- 22ms
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

  test₀ : ϕ (0ₕ _) ≡ true    -- 1,328ms (unlike for Klein, this works)
  test₀ = refl

{-
  test₁ : ϕ (ϕ⁻¹ true) ≡ true    -- nope
  test₁ = refl
-}


module CP2-test₂ where
  ϕ : coHom 2 CP² → ℤ
  ϕ = fun (fst H²CP²≅ℤ)

  ϕ⁻¹ : ℤ → coHom 2 CP²
  ϕ⁻¹ = inv (fst H²CP²≅ℤ)

  -- For explicitly constructed elements g : H²CP², ϕ works well
  test₀ : ϕ (0ₕ _) ≡ 0    -- <10ms
  test₀ = refl

  generator : coHom 2 CP²
  generator = ∣ (λ { (inl x) → ∣ x ∣ ; (inr x) → 0ₖ _ ; (push a i) → p a i}) ∣₂
    where
    ind : (B : TotalHopf → Type) → ((x : _) → isOfHLevel 3 (B x)) → B (north , base) → (x : _) → B x
    ind =
      transport (λ i → (B : isoToPath IsoS³TotalHopf i → Type)
        → ((x : _) → isOfHLevel 3 (B x))
          → B (transp (λ j → isoToPath IsoS³TotalHopf (i ∨ ~ j)) i (north , base)) → (x : _) → B x)
          λ B hLev ind → sphereElim _ (λ _ → hLev _) ind

    p : (a : TotalHopf) → ∣ fst a ∣ ≡ 0ₖ 2
    p = ind _ (λ _ → isOfHLevelTrunc 4 _ _) refl

  test₁ : ϕ generator ≡ 1     -- 24ms
  test₁ = refl


  -- For _+ₕ_ too
  test₂ : ϕ (ϕ⁻¹ 0 +ₕ ϕ⁻¹ 0) ≡ 0     -- 1,343ms
  test₂ = refl

  test₃ : ϕ (ϕ⁻¹ 1 +ₕ ϕ⁻¹ 1) ≡ 2     -- 1,302ms
  test₃ = refl

  test₄ : ϕ (ϕ⁻¹ 2 +ₕ ϕ⁻¹ 2) ≡ 4     -- 1,410ms
  test₄ = refl


module CP2-test₄ where
  ϕ : coHom 4 CP² → ℤ
  ϕ = fun (fst H⁴CP²≅ℤ)

  ϕ⁻¹ : ℤ → coHom 4 CP²
  ϕ⁻¹ = inv (fst H⁴CP²≅ℤ)

{-
  test₀ : ϕ (0ₕ _) ≡ 0 -- fails already here...
  test₀ = refl
-}
