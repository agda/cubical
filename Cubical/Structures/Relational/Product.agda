{-

Product of structures S and T: X ↦ S X × T X

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Relational.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
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

ProductSetStructure : SetStructure ℓ ℓ₁ → SetStructure ℓ ℓ₂ → SetStructure ℓ (ℓ-max ℓ₁ ℓ₂)
ProductSetStructure S₁ S₂ .struct X = S₁ .struct X × S₂ .struct X
ProductSetStructure S₁ S₂ .set setX = isSet× (S₁ .set setX) (S₂ .set setX)

ProductPropRel :
  {S₁ : Type ℓ → Type ℓ₁} (ρ₁ : StrRel S₁ ℓ₁')
  {S₂ : Type ℓ → Type ℓ₂} (ρ₂ : StrRel S₂ ℓ₂')
  → StrRel (ProductStructure S₁ S₂) (ℓ-max ℓ₁' ℓ₂')
ProductPropRel ρ₁ ρ₂ .rel R (s₁ , s₂) (t₁ , t₂) =
  ρ₁ .rel R s₁ t₁ × ρ₂ .rel R s₂ t₂
ProductPropRel ρ₁ ρ₂ .prop propR (s₁ , s₂) (t₁ , t₂) =
  isProp× (ρ₁ .prop propR s₁ t₁) (ρ₂ .prop propR s₂ t₂)

open isUnivalentRel
open BisimDescends

productUnivalentRel :
  {S₁ : SetStructure ℓ ℓ₁} {ρ₁ : StrRel (S₁ .struct) ℓ₁'}
  {S₂ : SetStructure ℓ ℓ₂} {ρ₂ : StrRel (S₂ .struct) ℓ₂'}
  → isUnivalentRel S₁ ρ₁ → isUnivalentRel S₂ ρ₂
  → isUnivalentRel (ProductSetStructure S₁ S₂) (ProductPropRel ρ₁ ρ₂)
productUnivalentRel {ρ₁ = ρ₁} {ρ₂ = ρ₂} θ₁ θ₂ .propQuo R (t , r) (t' , r') =
  equivFun ΣPath≃PathΣ
    ( equivFun ΣPath≃PathΣ
      ( cong fst (θ₁ .propQuo R (t .fst , r .fst) (t' .fst , r' .fst))
      , cong fst (θ₂ .propQuo R (t .snd , r .snd) (t' .snd , r' .snd))
      )
    , isProp→PathP (λ _ → ProductPropRel ρ₁ ρ₂ .prop (λ _ _ → squash/ _ _) _ _) _ _
    )
productUnivalentRel θ₁ θ₂ .descends _ .fst (code₁ , code₂) .quoᴸ .fst =
  θ₁ .descends _ .fst code₁ .quoᴸ .fst , θ₂ .descends _ .fst code₂ .quoᴸ .fst
productUnivalentRel θ₁ θ₂ .descends _  .fst (code₁ , code₂) .quoᴸ .snd =
  θ₁ .descends _ .fst code₁ .quoᴸ .snd , θ₂ .descends _ .fst code₂ .quoᴸ .snd
productUnivalentRel θ₁ θ₂ .descends _ .fst (code₁ , code₂) .quoᴿ .fst =
  θ₁ .descends _ .fst code₁ .quoᴿ .fst , θ₂ .descends _ .fst code₂ .quoᴿ .fst
productUnivalentRel θ₁ θ₂ .descends _ .fst (code₁ , code₂) .quoᴿ .snd =
  θ₁ .descends _ .fst code₁ .quoᴿ .snd , θ₂ .descends _ .fst code₂ .quoᴿ .snd
productUnivalentRel θ₁ θ₂ .descends _ .fst (code₁ , code₂) .path =
  equivFun ΣPathP≃PathPΣ (θ₁ .descends _ .fst code₁ .path , θ₂ .descends _ .fst code₂ .path)
productUnivalentRel θ₁ θ₂ .descends {A = X , s} {B = Y , t} R .snd d =
  θ₁ .descends R .snd d₁ , θ₂ .descends R .snd d₂
  where
  d₁ : BisimDescends _ _ (X , s .fst) (Y , t .fst) R
  d₁ .quoᴸ = d .quoᴸ .fst .fst , d .quoᴸ .snd .fst
  d₁ .quoᴿ = d .quoᴿ .fst .fst , d .quoᴿ .snd .fst
  d₁ .path i = d .path i .fst

  d₂ : BisimDescends _ _ (X , s .snd) (Y , t .snd) R
  d₂ .quoᴸ = d .quoᴸ .fst .snd , d .quoᴸ .snd .snd
  d₂ .quoᴿ = d .quoᴿ .fst .snd , d .quoᴿ .snd .snd
  d₂ .path i = d .path i .snd

