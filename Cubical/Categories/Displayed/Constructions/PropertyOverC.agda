-- | Property displayed over a category.
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.PropertyOverC where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Constructions.StructureOverC
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓS ℓR : Level

open Category
open Functor
open Categoryᴰ
open Functorᴰ

module _ (C : Category ℓC ℓC') (P : Category.ob C → Type ℓP) where
  private
    module C = Category C
  open Category
  open Functor

  PropertyOverC : Categoryᴰ C ℓP ℓ-zero
  PropertyOverC = StructureOverC→Catᴰ struct where
    open StructureOverC
    struct : StructureOverC C ℓP ℓ-zero
    struct .ob[_] = P
    struct .Hom[_][_,_] _ _ _ = Unit
    struct .idᴰ = tt
    struct ._⋆ᴰ_ = λ _ _ → tt
    struct .isPropHomᴰ = isPropUnit

  hasContrHomsPropertyOverC : hasContrHoms PropertyOverC 
  hasContrHomsPropertyOverC _ _ _ = isContrUnit

  module _ {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
           (F : Functor D C)
           (F-obᴰ : {x : D .ob} →
             Dᴰ .ob[_] x → ob[ PropertyOverC ] (F .F-ob x))
           where
    intro : Functorᴰ F Dᴰ PropertyOverC
    intro =
      mkContrHomsFunctor hasContrHomsPropertyOverC F-obᴰ
