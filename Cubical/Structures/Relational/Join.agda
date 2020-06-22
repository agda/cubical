{-

Join of structures S and T: X ↦ S X × T X

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Relational.Join where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.RelationalStructure
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients

open import Cubical.Foundations.SIP

private
  variable
    ℓ ℓ₁ ℓ₁' ℓ₂ ℓ₂' : Level

-- Structured relations

join-setStructure : SetStructure ℓ ℓ₁ → SetStructure ℓ ℓ₂ → SetStructure ℓ (ℓ-max ℓ₁ ℓ₂)
join-setStructure S₁ S₂ .struct X = S₁ .struct X × S₂ .struct X
join-setStructure S₁ S₂ .set setX = isSet× (S₁ .set setX) (S₂ .set setX)

join-propRel :
  {S₁ : Type ℓ → Type ℓ₁} (ρ₁ : StrRel S₁ ℓ₁')
  {S₂ : Type ℓ → Type ℓ₂} (ρ₂ : StrRel S₂ ℓ₂')
  → StrRel (join-structure S₁ S₂) (ℓ-max ℓ₁' ℓ₂')
join-propRel ρ₁ ρ₂ .rel X Y R (s₁ , s₂) (t₁ , t₂) =
  ρ₁ .rel X Y R s₁ t₁
  × ρ₂ .rel X Y R s₂ t₂
join-propRel ρ₁ ρ₂ .prop propR (s₁ , s₂) (t₁ , t₂) =
  isProp× (ρ₁ .prop propR s₁ t₁) (ρ₂ .prop propR s₂ t₂)

open isSNRS
open BisimDescends

isSNRSJoin :
  (S₁ : SetStructure ℓ ℓ₁) {ρ₁ : StrRel (S₁ .struct) ℓ₁'}
  (S₂ : SetStructure ℓ ℓ₂) {ρ₂ : StrRel (S₂ .struct) ℓ₂'}
  → isSNRS S₁ ρ₁ → isSNRS S₂ ρ₂
  → isSNRS (join-setStructure S₁ S₂) (join-propRel ρ₁ ρ₂)
isSNRSJoin _ {ρ₁} _ {ρ₂} θ₁ θ₂ .propQuo R (t , r) (t' , r') =
  equivFun ΣPath≃PathΣ
    ( equivFun ΣPath≃PathΣ
      ( cong fst (θ₁ .propQuo R (t .fst , r .fst) (t' .fst , r' .fst))
      , cong fst (θ₂ .propQuo R (t .snd , r .snd) (t' .snd , r' .snd))
      )
    , isProp→PathP (λ _ → join-propRel ρ₁ ρ₂ .prop (λ _ _ → squash/ _ _) _ _) _ _
    )
isSNRSJoin _ _ θ₁ θ₂ .descends _ .fst (code₁ , code₂) .quoᴸ .fst =
  θ₁ .descends _ .fst code₁ .quoᴸ .fst , θ₂ .descends _ .fst code₂ .quoᴸ .fst
isSNRSJoin _ _ θ₁ θ₂ .descends _  .fst (code₁ , code₂) .quoᴸ .snd =
  θ₁ .descends _ .fst code₁ .quoᴸ .snd , θ₂ .descends _ .fst code₂ .quoᴸ .snd
isSNRSJoin _ _ θ₁ θ₂ .descends _ .fst (code₁ , code₂) .quoᴿ .fst =
  θ₁ .descends _ .fst code₁ .quoᴿ .fst , θ₂ .descends _ .fst code₂ .quoᴿ .fst
isSNRSJoin _ _ θ₁ θ₂ .descends _ .fst (code₁ , code₂) .quoᴿ .snd =
  θ₁ .descends _ .fst code₁ .quoᴿ .snd , θ₂ .descends _ .fst code₂ .quoᴿ .snd
isSNRSJoin _ _ θ₁ θ₂ .descends _ .fst (code₁ , code₂) .path =
  equivFun ΣPathP≃PathPΣ (θ₁ .descends _ .fst code₁ .path , θ₂ .descends _ .fst code₂ .path)
isSNRSJoin _ {ρ₁} _ {ρ₂} θ₁ θ₂ .descends {A = X , s} {B = Y , t} R .snd d =
  θ₁ .descends R .snd d₁ , θ₂ .descends R .snd d₂
  where
  d₁ : BisimDescends _ ρ₁ (X , s .fst) (Y , t .fst) R
  d₁ .quoᴸ = d .quoᴸ .fst .fst , d .quoᴸ .snd .fst
  d₁ .quoᴿ = d .quoᴿ .fst .fst , d .quoᴿ .snd .fst
  d₁ .path i = d .path i .fst

  d₂ : BisimDescends _ ρ₂ (X , s .snd) (Y , t .snd) R
  d₂ .quoᴸ = d .quoᴸ .fst .snd , d .quoᴸ .snd .snd
  d₂ .quoᴿ = d .quoᴿ .fst .snd , d .quoᴿ .snd .snd
  d₂ .path i = d .path i .snd

