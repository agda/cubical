{-

Product of structures S and T: X ↦ S X × T X

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Relational.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients

open import Cubical.Structures.Product

private
  variable
    ℓ ℓ₁ ℓ₁' ℓ₂ ℓ₂' : Level

-- Structured relations

ProductRelStr :
  {S₁ : Type ℓ → Type ℓ₁} (ρ₁ : StrRel S₁ ℓ₁')
  {S₂ : Type ℓ → Type ℓ₂} (ρ₂ : StrRel S₂ ℓ₂')
  → StrRel (ProductStructure S₁ S₂) (ℓ-max ℓ₁' ℓ₂')
ProductRelStr ρ₁ ρ₂ R (s₁ , s₂) (t₁ , t₂) =
  ρ₁ R s₁ t₁ × ρ₂ R s₂ t₂

open SuitableStrRel

productSuitableRel :
  {S₁ : Type ℓ → Type ℓ₁} {ρ₁ : StrRel S₁ ℓ₁'}
  {S₂ : Type ℓ → Type ℓ₂} {ρ₂ : StrRel S₂ ℓ₂'}
  → SuitableStrRel S₁ ρ₁ → SuitableStrRel S₂ ρ₂
  → SuitableStrRel (ProductStructure S₁ S₂) (ProductRelStr ρ₁ ρ₂)
productSuitableRel θ₁ θ₂ .quo (X , s₁ , s₂) R (r₁ , r₂) .fst .fst =
  θ₁ .quo (X , s₁) R r₁ .fst .fst , θ₂ .quo (X , s₂) R r₂ .fst .fst
productSuitableRel θ₁ θ₂ .quo (X , s₁ , s₂) R (r₁ , r₂) .fst .snd =
  θ₁ .quo (X , s₁) R r₁ .fst .snd , θ₂ .quo (X , s₂) R r₂ .fst .snd
productSuitableRel θ₁ θ₂ .quo (X , s₁ , s₂) R (r₁ , r₂) .snd ((q₁ , q₂) , (c₁ , c₂)) i .fst =
  θ₁ .quo (X , s₁) R r₁ .snd (q₁ , c₁) i .fst , θ₂ .quo (X , s₂) R r₂ .snd (q₂ , c₂) i .fst
productSuitableRel θ₁ θ₂ .quo (X , s₁ , s₂) R (r₁ , r₂) .snd ((q₁ , q₂) , (c₁ , c₂)) i .snd =
  θ₁ .quo (X , s₁) R r₁ .snd (q₁ , c₁) i .snd , θ₂ .quo (X , s₂) R r₂ .snd (q₂ , c₂) i .snd
productSuitableRel θ₁ θ₂ .symmetric R (r₁ , r₂) =
  θ₁ .symmetric R r₁ , θ₂ .symmetric R r₂
productSuitableRel θ₁ θ₂ .transitive R R' (r₁ , r₂) (r₁' , r₂') =
  θ₁ .transitive R R' r₁ r₁' , θ₂ .transitive R R' r₂ r₂'
productSuitableRel θ₁ θ₂ .set setX =
  isSet× (θ₁ .set setX) (θ₂ .set setX)
productSuitableRel θ₁ θ₂ .prop propR (s₁ , s₂) (t₁ , t₂) =
  isProp× (θ₁ .prop propR s₁ t₁) (θ₂ .prop propR s₂ t₂)

productRelMatchesEquiv :
  {S₁ : Type ℓ → Type ℓ₁} (ρ₁ : StrRel S₁ ℓ₁') {ι₁ : StrEquiv S₁ ℓ₁'}
  {S₂ : Type ℓ → Type ℓ₂} (ρ₂ : StrRel S₂ ℓ₂') {ι₂ : StrEquiv S₂ ℓ₂'}
  → StrRelMatchesEquiv ρ₁ ι₁ → StrRelMatchesEquiv ρ₂ ι₂
  → StrRelMatchesEquiv (ProductRelStr ρ₁ ρ₂) (ProductEquivStr ι₁ ι₂)
productRelMatchesEquiv ρ₁ ρ₂ μ₁ μ₂ A B e =
  Σ-cong-equiv (μ₁ _ _ e) (λ _ → μ₂ _ _ e)
