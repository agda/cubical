module Cubical.Categories.Displayed.Instances.Terminal.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Terminal

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Categoryᴰ
open Section

-- Terminal category over a base category
Unitᴰ : (C : Category ℓC ℓC') → Categoryᴰ C ℓ-zero ℓ-zero
Unitᴰ C .ob[_] x = Unit
Unitᴰ C .Hom[_][_,_] f tt tt = Unit
Unitᴰ C .idᴰ = tt
Unitᴰ C ._⋆ᴰ_ = λ _ _ → tt
Unitᴰ C .⋆IdLᴰ fᴰ i = tt
Unitᴰ C .⋆IdRᴰ fᴰ i = tt
Unitᴰ C .⋆Assocᴰ fᴰ gᴰ hᴰ i = tt
Unitᴰ C .isSetHomᴰ x y x₁ y₁ i i₁ = tt

-- Terminal category over the terminal category
UnitCᴰ : Categoryᴰ (TerminalCategory {ℓ-zero}) ℓ-zero ℓ-zero
UnitCᴰ = Unitᴰ TerminalCategory

module _ {C : Category ℓC ℓC'} where
  hasContrHomsUnitᴰ : hasContrHoms (Unitᴰ C)
  hasContrHomsUnitᴰ = hasContrHomsPropertyOver C _

  ttS : GlobalSection (Unitᴰ C)
  ttS .F-obᴰ  = λ _ → tt
  ttS .F-homᴰ = λ _ → tt
  ttS .F-idᴰ  = refl
  ttS .F-seqᴰ _ _ = refl

