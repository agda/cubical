{-

A parameterized family of structures S can be combined into a single structure:
X ↦ (a : A) → S a X

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Relational.Parameterized where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.RelationalStructure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients

open import Cubical.Structures.Parameterized

private
  variable
    ℓ ℓ₀ ℓ₁ ℓ₁' : Level

-- Structured relations

module _ (A : Type ℓ₀) where

  param-setStructure : (A → SetStructure ℓ ℓ₁) → SetStructure ℓ (ℓ-max ℓ₀ ℓ₁)
  param-setStructure S .struct X = (a : A) → (S a .struct X)
  param-setStructure S .set setX = isSetΠ λ a → S a .set setX

  param-propRel : {S : A → Type ℓ → Type ℓ₁} {ℓ₁' : Level}
    → (∀ a → StrRel (S a) ℓ₁')
    → StrRel (ParamStructure A S) (ℓ-max ℓ₀ ℓ₁')
  param-propRel ρ .rel R s t =
    (a : A) → ρ a .rel R (s a) (t a)
  param-propRel ρ .prop propR s t =
    isPropΠ λ a → ρ a .prop propR (s a) (t a)

  open isSNRS
  open BisimDescends

  isSNRSParam : {S : A → SetStructure ℓ ℓ₁} {ℓ₁' : Level}
    {ρ : ∀ a → StrRel (S a .struct) ℓ₁'}
    → (∀ a → isSNRS (S a) (ρ a))
    → isSNRS (param-setStructure S) (param-propRel ρ)
  isSNRSParam {ρ = ρ} θ .propQuo R f f' =
    equivFun ΣPath≃PathΣ
      ( funExt (λ a → cong fst (θ a .propQuo R (f .fst a , f .snd a) (f' .fst a , f' .snd a)))
      , isProp→PathP (λ _ → param-propRel ρ .prop (λ _ _ → squash/ _ _) _ _) _ _
      )
  isSNRSParam θ .descends _ .fst code .quoᴸ .fst a =
    θ a .descends _ .fst (code a) .quoᴸ .fst
  isSNRSParam θ .descends _ .fst code .quoᴸ .snd a =
    θ a .descends _ .fst (code a) .quoᴸ .snd
  isSNRSParam θ .descends _ .fst code .quoᴿ .fst a =
    θ a .descends _ .fst (code a) .quoᴿ .fst
  isSNRSParam θ .descends _ .fst code .quoᴿ .snd a =
    θ a .descends _ .fst (code a) .quoᴿ .snd
  isSNRSParam θ .descends _ .fst code .path =
    funExt λ a → θ a .descends _ .fst (code a) .path
  isSNRSParam θ .descends {A = X , f} {B = Y , g} R .snd d a =
    θ a .descends R .snd d'
    where
    d' : BisimDescends _ _ (X , f a) (Y , g a) R
    d' .quoᴸ = d .quoᴸ .fst a , d .quoᴸ .snd a
    d' .quoᴿ = d .quoᴿ .fst a , d .quoᴿ .snd a
    d' .path i = d .path i a

