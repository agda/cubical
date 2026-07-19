-- | Property displayed over a category.
module Cubical.Categories.Displayed.Constructions.PropertyOver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.StructureOver.Base

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

  PropertyOver : Categoryᴰ C ℓP ℓ-zero
  PropertyOver = StructureOver→Catᴰ struct where
    open StructureOver
    struct : StructureOver C ℓP ℓ-zero
    struct .ob[_] = P
    struct .Hom[_][_,_] _ _ _ = Unit
    struct .idᴰ = tt
    struct ._⋆ᴰ_ = λ _ _ → tt
    struct .isPropHomᴰ = isPropUnit

  hasContrHomsPropertyOver : hasContrHoms PropertyOver
  hasContrHomsPropertyOver _ _ _ = isContrUnit

  module _ {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
           (F : Functor D C)
           (F-obᴰ : {x : D .ob} →
             Dᴰ .ob[_] x → ob[ PropertyOver ] (F .F-ob x))
           where
    intro : Functorᴰ F Dᴰ PropertyOver
    intro =
      mkContrHomsFunctor hasContrHomsPropertyOver F-obᴰ
