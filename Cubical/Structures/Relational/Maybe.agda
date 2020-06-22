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

maybe-setStructure : SetStructure ℓ ℓ₁ → SetStructure ℓ ℓ₁
maybe-setStructure S .struct X = Maybe (S .struct X)
maybe-setStructure S .set setX = isOfHLevelMaybe 0 (S .set setX)

maybe-propRel : {S : Type ℓ → Type ℓ₁} {ℓ₁' : Level}
  → StrRel S ℓ₁' → StrRel (λ X → Maybe (S X)) ℓ₁'
maybe-propRel ρ .rel X Y R = maybe-rel (ρ .rel X Y R)
maybe-propRel ρ .prop propR nothing nothing = isOfHLevelLift 1 isPropUnit
maybe-propRel ρ .prop propR nothing (just y) = isOfHLevelLift 1 isProp⊥
maybe-propRel ρ .prop propR (just x) nothing = isOfHLevelLift 1 isProp⊥
maybe-propRel ρ .prop propR (just x) (just y) = ρ .prop propR x y

open isSNRS
open BisimDescends

isSNRSMaybe : (S : SetStructure ℓ ℓ₁) (ρ : StrRel (S .struct) ℓ₁')
  → isSNRS S ρ
  → isSNRS (maybe-setStructure S) (maybe-propRel ρ)
isSNRSMaybe S ρ θ .propQuo {X , nothing} R (nothing , lift tt) (nothing , lift tt) = refl
isSNRSMaybe S ρ θ .propQuo {X , just x} R (just x' , p) (just y' , q) =
  cong (λ {(z , r) → (just z , r)}) (θ .propQuo R (x' , p) (y' , q))
isSNRSMaybe S ρ θ .descends {X , nothing} R .fst code .quoᴸ = nothing , _
isSNRSMaybe S ρ θ .descends {X , just x} {Y , just y} R .fst code .quoᴸ =
  just (θ .descends R .fst code .quoᴸ .fst) , θ .descends R .fst code .quoᴸ .snd
isSNRSMaybe S ρ θ .descends {B = Y , nothing} R .fst code .quoᴿ = nothing , _
isSNRSMaybe S ρ θ .descends {X , just x} {Y , just y} R .fst code .quoᴿ =
  just (θ .descends R .fst code .quoᴿ .fst) , θ .descends R .fst code .quoᴿ .snd
isSNRSMaybe S ρ θ .descends {X , nothing} {Y , nothing} R .fst code .path i = nothing
isSNRSMaybe S ρ θ .descends {X , just x} {Y , just y} R .fst code .path i =
  just (θ .descends R .fst code .path i)
isSNRSMaybe S ρ θ .descends {X , nothing} {Y , nothing} R .snd d = _
isSNRSMaybe S ρ θ .descends {X , nothing} {Y , just y} R .snd d with d .quoᴸ | d .quoᴿ | d .path
... | nothing , _ | just y' , _ | p = lift (MaybePathP.encode _ _ _ p .lower)
isSNRSMaybe S ρ θ .descends {X , just x} {Y , nothing} R .snd d with d .quoᴸ | d .quoᴿ | d .path
... | just x' , _ | nothing , _ | p = lift (MaybePathP.encode _ _ _ p .lower)
isSNRSMaybe S ρ θ .descends {X , just x} {Y , just y} R .snd d with d .quoᴸ | d .quoᴿ | d .path
... | just x' , c | just y' , c' | p =
  θ .descends R .snd d'
  where
  d' : BisimDescends (S .struct) ρ (X , x) (Y , y) R
  d' .quoᴸ = x' , c
  d' .quoᴿ = y' , c'
  d' .path = MaybePathP.encode _ _ _ p
