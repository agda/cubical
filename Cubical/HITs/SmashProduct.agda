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

-- Commutativity:
comm : {A B : ptType} → Smash A B → Smash B A
comm {A} {B} basel       = proj (pt B) (pt A)
comm {A} {B} baser       = proj (pt B) (pt A)
comm (proj x y)          = proj y x
comm {A} (gluel a i)     = compPath (gluer a) (sym (gluer (pt A))) i
comm {B = B} (gluer b i) = compPath (gluel b) (sym (gluel (pt B))) i

commK : ∀ {A B : ptType} → (x : Smash A B) → comm (comm x) ≡ x
commK {A} basel = gluel (pt A)
commK {B = B} baser = gluer (pt B)
commK (proj x y)  = refl
commK (gluel a i) = {!!}
commK (gluer b i) = {!!}

-- commK (A B : ptType) : (x : smash A B) -> Path (smash A B) (comm B A (comm A B x)) x = undefined
