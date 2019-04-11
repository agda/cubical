{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SmashProduct.Base where

open import Cubical.Foundations.Prelude

-- This should be upstreamed to Basics when we develop some theory
-- about pointed types
ptType : Type₁
ptType = Σ[ A ∈ Type₀ ] A

pt : ∀ (A : ptType) → A .fst
pt A = A .snd

data Smash (A B : ptType) : Type₀ where
  basel : Smash A B
  baser : Smash A B
  proj  : (x : A .fst) → (y : B .fst) → Smash A B
  gluel : (a : A .fst) → proj a (pt B) ≡ basel
  gluer : (b : B .fst) → proj (pt A) b ≡ baser

-- Commutativity
comm : {A B : ptType} → Smash A B → Smash B A
comm basel       = baser
comm baser       = basel
comm (proj x y)  = proj y x
comm (gluel a i) = gluer a i
comm (gluer b i) = gluel b i

commK : ∀ {A B : ptType} → (x : Smash A B) → comm (comm x) ≡ x
commK basel       = refl
commK baser       = refl
commK (proj x y)  = refl
commK (gluel a x) = refl
commK (gluer b x) = refl

-- WIP below

SmashPt : (A B : ptType) → ptType
SmashPt A B = (Smash A B , basel)

-- -- A (B C) = C (B A) = C (A B) = (A B) C
-- rearrange : ∀ {A B C : ptType} → Smash A (SmashPt B C) → Smash C (SmashPt B A)
-- rearrange basel = baser
-- rearrange baser = basel
-- rearrange {B = B} {C = C} (proj x basel) = proj (C .snd) baser
-- rearrange {C = C} (proj x baser) = proj (C .snd) basel  -- ?
-- rearrange (proj x (proj y z)) = proj z (proj y x)
-- rearrange {C = C} (proj x (gluel a i)) = proj (C .snd) {!!}
-- rearrange (proj x (gluer b i)) = {!!}
-- rearrange (gluel a i) = {!!}
-- rearrange (gluer b i) = {!gluel ? i!}

