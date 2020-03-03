{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SmashProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

data Smash (A B : Pointed₀) : Type₀ where
  basel : Smash A B
  baser : Smash A B
  proj  : (x : typ A) → (y : typ B) → Smash A B
  gluel : (a : typ A) → proj a (pt B) ≡ basel
  gluer : (b : typ B) → proj (pt A) b ≡ baser

-- Commutativity
comm : {A B : Pointed₀} → Smash A B → Smash B A
comm basel       = baser
comm baser       = basel
comm (proj x y)  = proj y x
comm (gluel a i) = gluer a i
comm (gluer b i) = gluel b i

commK : ∀ {A B : Pointed₀} → (x : Smash A B) → comm (comm x) ≡ x
commK basel       = refl
commK baser       = refl
commK (proj x y)  = refl
commK (gluel a x) = refl
commK (gluer b x) = refl

-- WIP below

SmashPt : (A B : Pointed₀) → Pointed₀
SmashPt A B = (Smash A B , basel)

-- -- A (B C) = C (B A) = C (A B) = (A B) C
-- rearrange : ∀ {A B C : Pointed₀} → Smash A (SmashPt B C) → Smash C (SmashPt B A)
-- rearrange basel = baser
-- rearrange baser = basel
-- rearrange {B = B} {C = C} (proj x basel) = proj (pt C) baser
-- rearrange {C = C} (proj x baser) = proj (pt C) basel  -- ?
-- rearrange (proj x (proj y z)) = proj z (proj y x)
-- rearrange {C = C} (proj x (gluel a i)) = proj (pt C) {!!}
-- rearrange (proj x (gluer b i)) = {!!}
-- rearrange (gluel a i) = {!!}
-- rearrange (gluer b i) = {!gluel ? i!}

