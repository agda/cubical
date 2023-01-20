{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓC' ℓC₀ ℓC₀' ℓD₀ ℓD₀' ℓC₁ ℓC₁' ℓD₁ ℓD₁' : Level

-- Product of total categories
module _ {C₀ : Category ℓC₀ ℓC₀'} {C₁ : Category ℓC₁ ℓC₁'}
  (D₀ : DisplayedCat C₀ ℓD₀ ℓD₀') (D₁ : DisplayedCat C₁ ℓD₁ ℓD₁')
  where

  private
    open DisplayedCat
    module D₀ = DisplayedCat D₀
    module D₁ = DisplayedCat D₁

  _×CD_ : DisplayedCat (C₀ ×C C₁) _ _
  _×CD_ .ob[_] (a₀ , a₁) = D₀.ob[ a₀ ] × D₁.ob[ a₁ ]
  _×CD_ .Hom[_][_,_] (f₀ , f₁) (d₀ , d₁) (e₀ , e₁) = D₀ [ f₀ ][ d₀ , e₀ ] × D₁ [ f₁ ][ d₁ , e₁ ]
  _×CD_ .idᴰ = D₀.idᴰ , D₁.idᴰ
  _×CD_ ._⋆ᴰ_ (f₀ , f₁) (g₀ , g₁) = (f₀ D₀.⋆ᴰ g₀) , (f₁ D₁.⋆ᴰ g₁)
  _×CD_ .⋆IdLᴰ _ = ΣPathP (D₀.⋆IdLᴰ _ , D₁.⋆IdLᴰ _)
  _×CD_ .⋆IdRᴰ _ = ΣPathP (D₀.⋆IdRᴰ _ , D₁.⋆IdRᴰ _)
  _×CD_ .⋆Assocᴰ _ _ _ = ΣPathP (D₀.⋆Assocᴰ _ _ _ , D₁.⋆Assocᴰ _ _ _)
  _×CD_ .isSetHomᴰ = isSet× D₀.isSetHomᴰ D₁.isSetHomᴰ

-- Product within a fiber
module _ {C : Category ℓC ℓC'}
  (D₀ : DisplayedCat C ℓD₀ ℓD₀') (D₁ : DisplayedCat C ℓD₁ ℓD₁')
  where

  private
    open DisplayedCat
    module D₀ = DisplayedCat D₀
    module D₁ = DisplayedCat D₁

  _×D_ : DisplayedCat C _ _
  _×D_ .ob[_] a = D₀.ob[ a ] × D₁.ob[ a ]
  _×D_ .Hom[_][_,_] f (d₀ , d₁) (e₀ , e₁) = D₀ [ f ][ d₀ , e₀ ] × D₁ [ f ][ d₁ , e₁ ]
  _×D_ .idᴰ = D₀.idᴰ , D₁.idᴰ
  _×D_ ._⋆ᴰ_ (f₀ , f₁) (g₀ , g₁) = (f₀ D₀.⋆ᴰ g₀) , (f₁ D₁.⋆ᴰ g₁)
  _×D_ .⋆IdLᴰ _ = ΣPathP (D₀.⋆IdLᴰ _ , D₁.⋆IdLᴰ _)
  _×D_ .⋆IdRᴰ _ = ΣPathP (D₀.⋆IdRᴰ _ , D₁.⋆IdRᴰ _)
  _×D_ .⋆Assocᴰ _ _ _ = ΣPathP (D₀.⋆Assocᴰ _ _ _ , D₁.⋆Assocᴰ _ _ _)
  _×D_ .isSetHomᴰ = isSet× D₀.isSetHomᴰ D₁.isSetHomᴰ
