{-

Equalizer of functions f g : S X ⇉ T X such that f and g act on relation structures

-}
{-# OPTIONS --safe #-}
module Cubical.Structures.Relational.Equalizer where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.RelationalStructure
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation as Trunc
open import Cubical.Relation.Binary.Base

private
  variable
    ℓ ℓ₁ ℓ₁' ℓ₂ ℓ₂' : Level

EqualizerStructure : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  (f g : ∀ X → S X → T X)
  → Type ℓ → Type (ℓ-max ℓ₁ ℓ₂)
EqualizerStructure {S = S} f g X = Σ[ s ∈ S X ] f X s ≡ g X s

EqualizerRelStr : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  {f g : ∀ X → S X → T X}
  → StrRel S ℓ₁' → StrRel T ℓ₂' → StrRel (EqualizerStructure f g) ℓ₁'
EqualizerRelStr ρ₁ ρ₂ R (s , _) (s' , _) = ρ₁ R s s'

equalizerSuitableRel : {S : Type ℓ → Type ℓ₁} {T : Type ℓ → Type ℓ₂}
  {f g : ∀ X → S X → T X}
  {ρ₁ : StrRel S ℓ₁'} {ρ₂ : StrRel T ℓ₂'}
  (αf : ∀ {X Y} {R : X → Y → Type ℓ} {s s'} → ρ₁ R s s' → ρ₂ R (f X s) (f Y s'))
  (αg : ∀ {X Y} {R : X → Y → Type ℓ} {s s'} → ρ₁ R s s' → ρ₂ R (g X s) (g Y s'))
  → SuitableStrRel S ρ₁
  → SuitableStrRel T ρ₂
  → SuitableStrRel (EqualizerStructure f g) (EqualizerRelStr ρ₁ ρ₂)
equalizerSuitableRel {f = f} {g} {ρ₁} {ρ₂} αf αg θ₁ θ₂ .quo (X , s , p) (R , qer) r =
  ( ((quo₁ .fst .fst , sym step₀ ∙ step₁) , quo₁ .fst .snd)
  , λ {((s' , _) , r') →
    Σ≡Prop (λ _ → θ₁ .prop (λ _ _ → squash/ _ _) _ _)
      (Σ≡Prop (λ _ → θ₂ .set squash/ _ _)
        (cong fst (quo₁ .snd (s' , r'))))}
  )
  where
  quo₁ = θ₁ .quo (X , s) (R , qer) r
  quo₂ = θ₂ .quo (X , f X s) (R , qer) (αf r)

  step₀ : quo₂ .fst .fst ≡ f (X / R .fst) (quo₁ .fst .fst)
  step₀ =
    cong fst
      (quo₂ .snd
        (f _ (quo₁ .fst .fst) , αf (quo₁ .fst .snd)))

  step₁ : quo₂ .fst .fst ≡ g (X / R .fst) (quo₁ .fst .fst)
  step₁ =
    cong fst
      (quo₂ .snd
        ( g _ (quo₁ .fst .fst)
        , subst (λ t → ρ₂ (graphRel [_]) t (g _ (quo₁ .fst .fst))) (sym p) (αg (quo₁ .fst .snd))
        ))
equalizerSuitableRel _ _ θ₁ _ .symmetric R = θ₁ .symmetric R
equalizerSuitableRel _ _ θ₁ _ .transitive R R' = θ₁ .transitive R R'
equalizerSuitableRel _ _ θ₁ θ₂ .set setX =
  isSetΣ (θ₁ .set setX) λ _ → isOfHLevelPath 2 (θ₂ .set setX) _ _
equalizerSuitableRel _ _ θ₁ _ .prop propR _ _ = θ₁ .prop propR _ _
