{-# OPTIONS --cubical #-}
module Cubical.HITs.SmashProduct where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

ptType : Set₁
ptType = Σ[ A ∈ Set ] A

pt : ∀ (A : ptType) → A .fst
pt A = A .snd

data Smash (A B : ptType) : Set where
  basel : Smash A B
  baser : Smash A B
  proj : (x : A .fst) → (y : B .fst) → Smash A B
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
commK {A} basel       = refl
commK {A} baser       = refl
commK {A} (proj x y)  = refl
commK {A} (gluel a x) = refl
commK {A} (gluer b x) = refl

-- WIP below

SmashPt : (A B : ptType) → ptType
SmashPt A B = (Smash A B , basel)

-- A (B C) = C (B A) = C (A B) = (A B) C
-- rearrange : ∀ {A B C : ptType} → Smash A (SmashPt B C) → Smash C (SmashPt B A)
-- rearrange = {!!}

