{-

  Maybe structure: X ↦ Maybe (S X)

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.Relational.Maybe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.RelationalStructure
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Maybe

open import Cubical.Structures.Maybe

private
  variable
    ℓ ℓ₁ ℓ₁' : Level

-- Structured relations

MaybeSetStructure : SetStructure ℓ ℓ₁ → SetStructure ℓ ℓ₁
MaybeSetStructure S .struct = MaybeStructure (S .struct)
MaybeSetStructure S .set setX = isOfHLevelMaybe 0 (S .set setX)

MaybePropRel : {S : Type ℓ → Type ℓ₁} {ℓ₁' : Level}
  → StrRel S ℓ₁' → StrRel (λ X → Maybe (S X)) ℓ₁'
MaybePropRel ρ .rel R = MaybeRel (ρ .rel R)
MaybePropRel ρ .prop propR nothing nothing = isOfHLevelLift 1 isPropUnit
MaybePropRel ρ .prop propR nothing (just y) = isOfHLevelLift 1 isProp⊥
MaybePropRel ρ .prop propR (just x) nothing = isOfHLevelLift 1 isProp⊥
MaybePropRel ρ .prop propR (just x) (just y) = ρ .prop propR x y

open isUnivalentRel
open BisimDescends

maybeUnivalentRel : {S : SetStructure ℓ ℓ₁} {ρ : StrRel (S .struct) ℓ₁'}
  → isUnivalentRel S ρ
  → isUnivalentRel (MaybeSetStructure S) (MaybePropRel ρ)
maybeUnivalentRel θ .propQuo {X , nothing} R (nothing , lift tt) (nothing , lift tt) = refl
maybeUnivalentRel θ .propQuo {X , just x} R (just x' , p) (just y' , q) =
  cong (λ {(z , r) → (just z , r)}) (θ .propQuo R (x' , p) (y' , q))
maybeUnivalentRel θ .descends {X , nothing} R .fst code .quoᴸ = nothing , _
maybeUnivalentRel θ .descends {X , just x} {Y , just y} R .fst code .quoᴸ =
  just (θ .descends R .fst code .quoᴸ .fst) , θ .descends R .fst code .quoᴸ .snd
maybeUnivalentRel θ .descends {B = Y , nothing} R .fst code .quoᴿ = nothing , _
maybeUnivalentRel θ .descends {X , just x} {Y , just y} R .fst code .quoᴿ =
  just (θ .descends R .fst code .quoᴿ .fst) , θ .descends R .fst code .quoᴿ .snd
maybeUnivalentRel θ .descends {X , nothing} {Y , nothing} R .fst code .path i = nothing
maybeUnivalentRel θ .descends {X , just x} {Y , just y} R .fst code .path i =
  just (θ .descends R .fst code .path i)
maybeUnivalentRel θ .descends {X , nothing} {Y , nothing} R .snd d = _
maybeUnivalentRel θ .descends {X , nothing} {Y , just y} R .snd d with d .quoᴸ | d .quoᴿ | d .path
... | nothing , _ | just y' , _ | p = lift (MaybePathP.encode _ _ _ p .lower)
maybeUnivalentRel θ .descends {X , just x} {Y , nothing} R .snd d with d .quoᴸ | d .quoᴿ | d .path
... | just x' , _ | nothing , _ | p = lift (MaybePathP.encode _ _ _ p .lower)
maybeUnivalentRel θ .descends {X , just x} {Y , just y} R .snd d with d .quoᴸ | d .quoᴿ | d .path
... | just x' , c | just y' , c' | p =
  θ .descends R .snd d'
  where
  d' : BisimDescends _ _ (X , x) (Y , y) R
  d' .quoᴸ = x' , c
  d' .quoᴿ = y' , c'
  d' .path = MaybePathP.encode _ _ _ p
