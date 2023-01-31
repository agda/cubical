{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Total where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD') where

  private
    open Category
    module C = Category C
    open Categoryᴰ D

  ∫ : Category (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
  ∫ .ob = Σ _ ob[_]
  ∫ .Hom[_,_] (_ , xᴰ) (_ , yᴰ) = Σ _ Hom[_][ xᴰ , yᴰ ]
  ∫ .id = _ , idᴰ
  ∫ ._⋆_ (_ , fᴰ) (_ , gᴰ) = _ , fᴰ ⋆ᴰ gᴰ
  ∫ .⋆IdL (_ , fᴰ) = ΣPathP (_ , ⋆IdLᴰ fᴰ)
  ∫ .⋆IdR (_ , fᴰ) = ΣPathP (_ , ⋆IdRᴰ fᴰ)
  ∫ .⋆Assoc (_ , fᴰ) (_ , gᴰ) (_ , hᴰ) = ΣPathP (_ , ⋆Assocᴰ fᴰ gᴰ hᴰ)
  ∫ .isSetHom = isSetΣ C.isSetHom (λ _ → isSetHomᴰ)
