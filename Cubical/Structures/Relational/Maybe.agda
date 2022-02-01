{-

Maybe structure: X ↦ Maybe (S X)

-}
{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Structures.Relational.Maybe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Trunc
open import Cubical.HITs.SetQuotients

open import Cubical.Structures.Maybe

private
  variable
    ℓ ℓ₁ ℓ₁' ℓ₁'' : Level

-- Structured relations

MaybeRelStr : {S : Type ℓ → Type ℓ₁} {ℓ₁' : Level}
  → StrRel S ℓ₁' → StrRel (λ X → Maybe (S X)) ℓ₁'
MaybeRelStr ρ R = MaybeRel (ρ R)

maybeSuitableRel : {S : Type ℓ → Type ℓ₁} {ρ : StrRel S ℓ₁'}
  → SuitableStrRel S ρ
  → SuitableStrRel (MaybeStructure S) (MaybeRelStr ρ)
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
maybeSuitableRel θ .set setX = isOfHLevelMaybe 0 (θ .set setX)
maybeSuitableRel θ .prop propR nothing nothing = isOfHLevelLift 1 isPropUnit
maybeSuitableRel θ .prop propR nothing (just y) = isOfHLevelLift 1 isProp⊥
maybeSuitableRel θ .prop propR (just x) nothing = isOfHLevelLift 1 isProp⊥
maybeSuitableRel θ .prop propR (just x) (just y) = θ .prop propR x y

maybeRelMatchesEquiv : {S : Type ℓ → Type ℓ₁} (ρ : StrRel S ℓ₁') {ι : StrEquiv S ℓ₁''}
  → StrRelMatchesEquiv ρ ι
  → StrRelMatchesEquiv (MaybeRelStr ρ) (MaybeEquivStr ι)
maybeRelMatchesEquiv ρ μ (X , nothing) (Y , nothing) _ = Lift≃Lift (idEquiv _)
maybeRelMatchesEquiv ρ μ (X , nothing) (Y , just y) _ = Lift≃Lift (idEquiv _)
maybeRelMatchesEquiv ρ μ (X , just x) (Y , nothing) _ = Lift≃Lift (idEquiv _)
maybeRelMatchesEquiv ρ μ (X , just x) (Y , just y) = μ (X , x) (Y , y)

maybeRelAction :
  {S : Type ℓ → Type ℓ₁} {ρ : StrRel S ℓ₁'}
  → StrRelAction ρ
  → StrRelAction (MaybeRelStr ρ)
maybeRelAction α .actStr f = map-Maybe (α .actStr f)
maybeRelAction α .actStrId s =
  funExt⁻ (cong map-Maybe (funExt (α .actStrId))) s ∙ map-Maybe-id s
maybeRelAction α .actRel h nothing nothing = _
maybeRelAction α .actRel h (just s) (just t) r = α .actRel h s t r

maybePositiveRel :
  {S : Type ℓ → Type ℓ₁} {ρ : StrRel S ℓ₁'} {θ : SuitableStrRel S ρ}
  → PositiveStrRel θ
  → PositiveStrRel (maybeSuitableRel θ)
maybePositiveRel σ .act = maybeRelAction (σ .act)
maybePositiveRel σ .reflexive nothing = _
maybePositiveRel σ .reflexive (just s) = σ .reflexive s
maybePositiveRel σ .detransitive R R' {nothing} {nothing} r = ∣ nothing , _ , _ ∣
maybePositiveRel σ .detransitive R R' {just s} {just u} rr' =
  Trunc.map (λ {(t , r , r') → just t , r , r'}) (σ .detransitive R R' rr')
maybePositiveRel {S = S} {ρ = ρ} {θ = θ} σ .quo {X} R =
  subst isEquiv
    (funExt
      (elimProp (λ _ → maybeSuitableRel θ .set squash/ _ _)
        (λ {nothing → refl; (just _) → refl})))
    (compEquiv (isoToEquiv isom) (congMaybeEquiv (_ , σ .quo R)) .snd)
  where
  fwd : Maybe (S X) / MaybeRel (ρ (R .fst .fst)) → Maybe (S X / ρ (R .fst .fst))
  fwd [ nothing ] = nothing
  fwd [ just s ] = just [ s ]
  fwd (eq/ nothing nothing r i) = nothing
  fwd (eq/ (just s) (just t) r i) = just (eq/ s t r i)
  fwd (squash/ _ _ p q i j) =
    isOfHLevelMaybe 0 squash/ _ _ (cong fwd p) (cong fwd q) i j

  bwd : Maybe (S X / ρ (R .fst .fst)) → Maybe (S X) / MaybeRel (ρ (R .fst .fst))
  bwd nothing = [ nothing ]
  bwd (just [ s ]) = [ just s ]
  bwd (just (eq/ s t r i)) = eq/ (just s) (just t) r i
  bwd (just (squash/ _ _ p q i j)) =
    squash/ _ _ (cong (bwd ∘ just) p) (cong (bwd ∘ just) q) i j

  open Iso
  isom : Iso (Maybe (S X) / MaybeRel (ρ (R .fst .fst))) (Maybe (S X / ρ (R .fst .fst)))
  isom .fun = fwd
  isom .inv = bwd
  isom .rightInv nothing = refl
  isom .rightInv (just x) =
    elimProp {P = λ x → fwd (bwd (just x)) ≡ just x}
      (λ _ → isOfHLevelMaybe 0 squash/ _ _)
      (λ _ → refl)
      x
  isom .leftInv = elimProp (λ _ → squash/ _ _) (λ {nothing → refl; (just _) → refl})

maybeRelMatchesTransp : {S : Type ℓ → Type ℓ₁}
  (ρ : StrRel S ℓ₁') (α : EquivAction S)
  → StrRelMatchesEquiv ρ (EquivAction→StrEquiv α)
  → StrRelMatchesEquiv (MaybeRelStr ρ) (EquivAction→StrEquiv (maybeEquivAction α))
maybeRelMatchesTransp _ _ μ (X , nothing) (Y , nothing) _ =
  isContr→Equiv (isOfHLevelLift 0 isContrUnit) isContr-nothing≡nothing
maybeRelMatchesTransp _ _ μ (X , nothing) (Y , just y) _ =
  uninhabEquiv lower ¬nothing≡just
maybeRelMatchesTransp _ _ μ (X , just x) (Y , nothing) _ =
  uninhabEquiv lower ¬just≡nothing
maybeRelMatchesTransp _ _ μ (X , just x) (Y , just y) e =
  compEquiv (μ (X , x) (Y , y) e) (_ , isEmbedding-just _ _)
