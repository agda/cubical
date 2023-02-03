{-

  Definition of something

-}
{-# OPTIONS --safe #-}
module Cubical.Displayed.Relation.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.SetQuotients as Quo
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.ZigZag.Base
open import Cubical.Displayed.Relation.Base
open import Cubical.Displayed.Relation.Sets

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

ℛ-QER-Pointed : ∀ {ℓ ℓ'} → RelCatᴰ (ℛ-Set-QER ℓ ℓ') (Pointedᴰ ℓ) ℓ' ℓ-zero
ℛ-QER-Pointed .ob[_] ((_ , R) , a , b) = R .fst .fst a b
ℛ-QER-Pointed .Hom[_][_,_] _ _ _ = Unit
ℛ-QER-Pointed .idᴰ = _
ℛ-QER-Pointed ._⋆ᴰ_ _ _ = _
ℛ-QER-Pointed .⋆IdLᴰ _ = refl
ℛ-QER-Pointed .⋆IdRᴰ _ = refl
ℛ-QER-Pointed .⋆Assocᴰ _ _ _ = refl
ℛ-QER-Pointed .isSetHomᴰ = isSetUnit

ℛ-≃-Pointed : ∀ {ℓ} → RelCatᴰ (ℛ-Set-≃ ℓ) (Pointedᴰ ℓ) ℓ ℓ-zero
ℛ-≃-Pointed .ob[_] ((_ , e) , a , b) = e .fst a ≡ b
ℛ-≃-Pointed .Hom[_][_,_] _ _ _ = Unit
ℛ-≃-Pointed .idᴰ = _
ℛ-≃-Pointed ._⋆ᴰ_ _ _ = _
ℛ-≃-Pointed .⋆IdLᴰ _ = refl
ℛ-≃-Pointed .⋆IdRᴰ _ = refl
ℛ-≃-Pointed .⋆Assocᴰ _ _ _ = refl
ℛ-≃-Pointed .isSetHomᴰ = isSetUnit
