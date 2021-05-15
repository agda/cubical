{-# OPTIONS --safe #-}
module Cubical.Experiments.ZCohomologyExperiments where
open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.WedgeOfSpheres
open import Cubical.Foundations.Prelude

open import Cubical.HITs.Truncation
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Pushout
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.Data.Int
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Group hiding (Int)

private

  ⋁-to : coHom 2 S²⋁S¹⋁S¹ → Int
  ⋁-to = Iso.fun (GroupIso.isom H²-S²⋁S¹⋁S¹)
  ⋁-from : Int → coHom 2 S²⋁S¹⋁S¹
  ⋁-from = Iso.inv (GroupIso.isom H²-S²⋁S¹⋁S¹)

  g : S²⋁S¹⋁S¹ → ∥ S₊ 2 ∥ 4
  g (inl x) = ∣ x ∣
  g (inr x) = 0ₖ 2
  g (push a i) = 0ₖ 2

  G = ∣ g ∣₂

{-
This computes:
⋁-to (⋁-from 1 +ₕ ⋁-from 1) ≡ 2
⋁-to = refl

We have ⋁-from 1 ≡ G and G is much simpler

But this does not compute:
test₀ : ⋁-to (G +ₕ G) ≡ 2
test₀ = refl

With the strange addition it does:
test₁ : ⋁-to (G +'ₕ G) ≡ 2
test₁ = refl
-}

-- Similar stuff happens with Sⁿ.
private
  S²-to : coHom 2 (S₊ 2) → Int
  S²-to = Iso.fun (GroupIso.isom (Hⁿ-Sⁿ≅ℤ 1))

  S²-from : Int → coHom 2 (S₊ 2)
  S²-from = Iso.inv (GroupIso.isom (Hⁿ-Sⁿ≅ℤ 1))

  one : coHom 2 (S₊ 2)
  one = ∣ ∣_∣ ∣₂

{-
Does not compute
test₂ : S²-to (S²-from 1 +ₕ S²-from 1) ≡ 2
test₂ = refl

But this does
test₂ : S²-to (S²-from 1 +'ₕ S²-from 1) ≡ 2
test₂ = refl

This doesn't
test₃ : S²-to (one +ₕ one) ≡ 2
test₃ = refl

But this does
test₃ : S²-to (one +'ₕ one) ≡ 2
test₃ = refl
-}
