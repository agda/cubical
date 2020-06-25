{-

  Maybe structure: X ↦ Maybe (S X)

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.Relational.Maybe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma

open import Cubical.Structures.Maybe

private
  variable
    ℓ ℓ₁ ℓ₁' : Level

-- Structured relations

preservesSetsMaybe : {S : Type ℓ → Type ℓ₁} → preservesSets S → preservesSets (MaybeStructure S)
preservesSetsMaybe p setX = isOfHLevelMaybe 0 (p setX)

MaybePropRel : {S : Type ℓ → Type ℓ₁} {ℓ₁' : Level}
  → StrRel S ℓ₁' → StrRel (λ X → Maybe (S X)) ℓ₁'
MaybePropRel ρ .rel R = MaybeRel (ρ .rel R)
MaybePropRel ρ .prop propR nothing nothing = isOfHLevelLift 1 isPropUnit
MaybePropRel ρ .prop propR nothing (just y) = isOfHLevelLift 1 isProp⊥
MaybePropRel ρ .prop propR (just x) nothing = isOfHLevelLift 1 isProp⊥
MaybePropRel ρ .prop propR (just x) (just y) = ρ .prop propR x y

open SuitableStrRel

maybeSuitableRel : {S : Type ℓ → Type ℓ₁} {ρ : StrRel S ℓ₁'}
  → SuitableStrRel S ρ
  → SuitableStrRel (MaybeStructure S) (MaybePropRel ρ)
maybeSuitableRel θ .quo (X , nothing) R _ .fst = nothing , _
maybeSuitableRel θ .quo (X , nothing) R _ .snd (nothing , _) = refl
maybeSuitableRel θ .quo (X , just s) R c .fst =
  just (θ .quo (X , s) R c .fst .fst) , θ .quo (X , s) R c .fst .snd
maybeSuitableRel θ .quo (X , just s) R c .snd (just s' , r) =
  cong (λ {(t , r') → just t , r'}) (θ .quo (X , s) R c .snd (s' , r))
maybeSuitableRel θ .symmetric R {nothing} {nothing} r = _
maybeSuitableRel θ .symmetric R {just s} {just t} r = θ .symmetric R r
maybeSuitableRel θ .transitive R R' {nothing} {nothing} {nothing} r r' = _
maybeSuitableRel θ .transitive R R' {just s} {just t} {just u} r r' = θ .transitive R R' r r'

maybeRelMatchesEquiv : {S : Type ℓ → Type ℓ₁} (ρ : StrRel S ℓ₁') {ι : StrEquiv S ℓ₁'}
  → StrRelMatchesEquiv ρ ι
  → StrRelMatchesEquiv (MaybePropRel ρ) (MaybeEquivStr ι)
maybeRelMatchesEquiv ρ μ (X , nothing) (Y , nothing) _ = idEquiv _
maybeRelMatchesEquiv ρ μ (X , nothing) (Y , just y) _ = idEquiv _
maybeRelMatchesEquiv ρ μ (X , just x) (Y , nothing) _ = idEquiv _
maybeRelMatchesEquiv ρ μ (X , just x) (Y , just y) = μ (X , x) (Y , y)
