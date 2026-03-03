module Cubical.Categories.Displayed.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓC' ℓC₀ ℓC₀' ℓD₀ ℓD₀' ℓC₁ ℓC₁' ℓD₁ ℓD₁' : Level

-- Product of total categories
module _ {C₀ : Category ℓC₀ ℓC₀'} {C₁ : Category ℓC₁ ℓC₁'}
  (D₀ : Categoryᴰ C₀ ℓD₀ ℓD₀') (D₁ : Categoryᴰ C₁ ℓD₁ ℓD₁')
  where

  private
    open Categoryᴰ
    module D₀ = Categoryᴰ D₀
    module D₁ = Categoryᴰ D₁

  _×Cᴰ_ : Categoryᴰ (C₀ ×C C₁) _ _
  _×Cᴰ_ .ob[_] (a₀ , a₁) = D₀.ob[ a₀ ] × D₁.ob[ a₁ ]
  _×Cᴰ_ .Hom[_][_,_] (f₀ , f₁) (d₀ , d₁) (e₀ , e₁) = D₀ [ f₀ ][ d₀ , e₀ ] × D₁ [ f₁ ][ d₁ , e₁ ]
  _×Cᴰ_ .idᴰ = D₀.idᴰ , D₁.idᴰ
  _×Cᴰ_ ._⋆ᴰ_ (f₀ , f₁) (g₀ , g₁) = (f₀ D₀.⋆ᴰ g₀) , (f₁ D₁.⋆ᴰ g₁)
  _×Cᴰ_ .⋆IdLᴰ _ = ΣPathP (D₀.⋆IdLᴰ _ , D₁.⋆IdLᴰ _)
  _×Cᴰ_ .⋆IdRᴰ _ = ΣPathP (D₀.⋆IdRᴰ _ , D₁.⋆IdRᴰ _)
  _×Cᴰ_ .⋆Assocᴰ _ _ _ = ΣPathP (D₀.⋆Assocᴰ _ _ _ , D₁.⋆Assocᴰ _ _ _)
  _×Cᴰ_ .isSetHomᴰ = isSet× D₀.isSetHomᴰ D₁.isSetHomᴰ

-- Product within a fiber
module _ {C : Category ℓC ℓC'}
  (D₀ : Categoryᴰ C ℓD₀ ℓD₀') (D₁ : Categoryᴰ C ℓD₁ ℓD₁')
  where

  private
    open Categoryᴰ
    module D₀ = Categoryᴰ D₀
    module D₁ = Categoryᴰ D₁

  _×ᴰ_ : Categoryᴰ C _ _
  _×ᴰ_ .ob[_] a = D₀.ob[ a ] × D₁.ob[ a ]
  _×ᴰ_ .Hom[_][_,_] f (d₀ , d₁) (e₀ , e₁) = D₀ [ f ][ d₀ , e₀ ] × D₁ [ f ][ d₁ , e₁ ]
  _×ᴰ_ .idᴰ = D₀.idᴰ , D₁.idᴰ
  _×ᴰ_ ._⋆ᴰ_ (f₀ , f₁) (g₀ , g₁) = (f₀ D₀.⋆ᴰ g₀) , (f₁ D₁.⋆ᴰ g₁)
  _×ᴰ_ .⋆IdLᴰ _ = ΣPathP (D₀.⋆IdLᴰ _ , D₁.⋆IdLᴰ _)
  _×ᴰ_ .⋆IdRᴰ _ = ΣPathP (D₀.⋆IdRᴰ _ , D₁.⋆IdRᴰ _)
  _×ᴰ_ .⋆Assocᴰ _ _ _ = ΣPathP (D₀.⋆Assocᴰ _ _ _ , D₁.⋆Assocᴰ _ _ _)
  _×ᴰ_ .isSetHomᴰ = isSet× D₀.isSetHomᴰ D₁.isSetHomᴰ
