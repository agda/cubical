{-

  Definition of something

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Displayed.Relation.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Adjoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Data.Unit
open import Cubical.Displayed.Relation.Base
open import Cubical.Displayed.Relation.Sets
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.ZigZag.Base

open Categoryᴰ

Pointedᴰ : ∀ ℓ → Categoryᴰ (SET ℓ) ℓ ℓ
Pointedᴰ ℓ .ob[_] A = A .fst
Pointedᴰ ℓ .Hom[_][_,_] f a b = f a ≡ b
Pointedᴰ ℓ .idᴰ = refl
Pointedᴰ ℓ ._⋆ᴰ_ p q = cong _ p ∙ q
Pointedᴰ ℓ .⋆IdLᴰ {y = A} _ = A .snd _ _ _ _
Pointedᴰ ℓ .⋆IdRᴰ {y = A} _ = A .snd _ _ _ _
Pointedᴰ ℓ .⋆Assocᴰ {w = A} _ _ _ = A .snd _ _ _ _
Pointedᴰ ℓ .isSetHomᴰ {y = A} = isProp→isSet (A .snd _ _)

ℛ-Pointed-QER : ∀ {ℓ ℓ'} → RelCatᴰ (ℛ-Set-QER ℓ ℓ') (Pointedᴰ ℓ) ℓ' ℓ-zero
ℛ-Pointed-QER .ob[_] ((_ , R) , a , b) = R .fst .fst a b
ℛ-Pointed-QER .Hom[_][_,_] _ _ _ = Unit
ℛ-Pointed-QER .idᴰ = _
ℛ-Pointed-QER ._⋆ᴰ_ _ _ = _
ℛ-Pointed-QER .⋆IdLᴰ _ = refl
ℛ-Pointed-QER .⋆IdRᴰ _ = refl
ℛ-Pointed-QER .⋆Assocᴰ _ _ _ = refl
ℛ-Pointed-QER .isSetHomᴰ = isSetUnit

ℛ-Pointed-≃ : ∀ {ℓ} → RelCatᴰ (ℛ-Set-≃ ℓ) (Pointedᴰ ℓ) ℓ ℓ-zero
ℛ-Pointed-≃ .ob[_] ((_ , e) , a , b) = e .fst a ≡ b
ℛ-Pointed-≃ .Hom[_][_,_] _ _ _ = Unit
ℛ-Pointed-≃ .idᴰ = _
ℛ-Pointed-≃ ._⋆ᴰ_ _ _ = _
ℛ-Pointed-≃ .⋆IdLᴰ _ = refl
ℛ-Pointed-≃ .⋆IdRᴰ _ = refl
ℛ-Pointed-≃ .⋆Assocᴰ _ _ _ = refl
ℛ-Pointed-≃ .isSetHomᴰ = isSetUnit

open Functorᴰ

Pointed-QER→≃ : ∀ {ℓ} → RelCatFunctorᴰ Set-QER→≃ (Pointedᴰ ℓ) (Pointedᴰ ℓ) ℛ-Pointed-QER ℛ-Pointed-≃
Pointed-QER→≃ .F-obᴰ ((a , b) , r) = ([ a ] , [ b ]) , QER→Equiv.relToFwd≡ _ r
Pointed-QER→≃ .F-homᴰ ((p , q) , _) = (cong [_] p , cong [_] q) , _
Pointed-QER→≃ .F-idᴰ = refl
Pointed-QER→≃ .F-seqᴰ _ _ =
  isProp→PathP (λ _ → isProp× (isProp× (squash/ _ _) (squash/ _ _)) isPropUnit) _ _

Pointed-≃→QER : ∀ {ℓ} → RelCatFunctorᴰ Set-≃→QER (Pointedᴰ ℓ) (Pointedᴰ ℓ) ℛ-Pointed-≃ ℛ-Pointed-QER
Pointed-≃→QER .F-obᴰ ((a , b) , p) = (a , b) , p
Pointed-≃→QER .F-homᴰ ((p , q) , _) = (p , q) , _
Pointed-≃→QER .F-idᴰ = refl
Pointed-≃→QER .F-seqᴰ _ _ = refl

open NatTransᴰ
open UnitCounitᴰ._⊣[_]_

Pointed-QER⊣≃ : ∀ {ℓ} →
  RelCatAdjointᴰ Set-QER⊣≃ (Pointedᴰ ℓ) (Pointedᴰ ℓ) ℛ-Pointed-QER ℛ-Pointed-≃ Pointed-QER→≃ Pointed-≃→QER
Pointed-QER⊣≃ .ηᴰ .N-obᴰ ((a₀ , a₁) , r) = (refl , refl) , _
Pointed-QER⊣≃ .ηᴰ .N-homᴰ _ =
  isProp→PathP (λ _ → isProp× (isProp× (squash/ _ _) (squash/ _ _)) isPropUnit) _ _
Pointed-QER⊣≃ .εᴰ .N-obᴰ ((a₀ , a₁) , p) = (refl , refl) , _
Pointed-QER⊣≃ .εᴰ .N-homᴰ {y = (B₀ , B₁) , _} _ =
  isProp→PathP (λ _ → isProp× (isProp× (B₀ .snd _ _) (B₁ .snd _ _)) isPropUnit) _ _
Pointed-QER⊣≃ .Δ₁ᴰ _ =
  isProp→PathP (λ _ → isProp× (isProp× (squash/ _ _) (squash/ _ _)) isPropUnit) _ _
Pointed-QER⊣≃ .Δ₂ᴰ {y = (B₀ , B₁) , _} _ =
  isProp→PathP (λ _ → isProp× (isProp× (B₀ .snd _ _) (B₁ .snd _ _)) isPropUnit) _ _
