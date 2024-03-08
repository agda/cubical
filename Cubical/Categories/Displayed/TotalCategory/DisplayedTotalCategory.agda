{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.TotalCategory.DisplayedTotalCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.TotalCategory.Base hiding (intro)

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

-- Displayed total category, i.e. Σ for displayed categories
module _ {C : Category ℓC ℓC'}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (Dᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
  where

  open Categoryᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  ∫Cᴰ : Categoryᴰ C (ℓ-max ℓCᴰ ℓDᴰ) (ℓ-max ℓCᴰ' ℓDᴰ')
  ∫Cᴰ .ob[_] x = Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] Dᴰ.ob[ x , xᴰ ]
  ∫Cᴰ .Hom[_][_,_] f (_ , zᴰ) (_ , wᴰ) = Σ[ fᴰ ∈ Cᴰ.Hom[ f ][ _ , _ ] ] Dᴰ.Hom[ f , fᴰ ][ zᴰ , wᴰ ]
  ∫Cᴰ .idᴰ = Cᴰ.idᴰ , Dᴰ.idᴰ
  ∫Cᴰ ._⋆ᴰ_ (_ , hᴰ) (_ , kᴰ) = _ , hᴰ Dᴰ.⋆ᴰ kᴰ
  ∫Cᴰ .⋆IdLᴰ _ = ΣPathP (_ , Dᴰ.⋆IdLᴰ _)
  ∫Cᴰ .⋆IdRᴰ _ = ΣPathP (_ , Dᴰ.⋆IdRᴰ _)
  ∫Cᴰ .⋆Assocᴰ _ _ _ = ΣPathP (_ , Dᴰ.⋆Assocᴰ _ _ _)
  ∫Cᴰ .isSetHomᴰ = isSetΣ Cᴰ.isSetHomᴰ (λ _ → Dᴰ.isSetHomᴰ)

-- Projection out of the displayed total category
module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Dᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
  where

  open Functorᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  Fstᴰ : Functorᴰ Id (∫Cᴰ Cᴰ Dᴰ) Cᴰ
  Fstᴰ .F-obᴰ = fst
  Fstᴰ .F-homᴰ = fst
  Fstᴰ .F-idᴰ = refl
  Fstᴰ .F-seqᴰ _ _ = refl

  -- Functor into the displayed total category
  module _ {E : Category ℓE ℓE'} (F : Functor E C)
           {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
           (Fᴰ : Functorᴰ F Eᴰ Cᴰ)
           (Gᴰ : Functorᴰ (∫F Fᴰ) (Unitᴰ (∫C Eᴰ)) Dᴰ)
           where

    intro : Functorᴰ F Eᴰ (∫Cᴰ Cᴰ Dᴰ)
    intro .F-obᴰ xᴰ = Fᴰ .F-obᴰ xᴰ , Gᴰ .F-obᴰ _
    intro .F-homᴰ fᴰ = (Fᴰ .F-homᴰ fᴰ) , (Gᴰ .F-homᴰ _)
    intro .F-idᴰ = ΣPathP (Fᴰ .F-idᴰ , Gᴰ .F-idᴰ)
    intro .F-seqᴰ fᴰ gᴰ = ΣPathP (Fᴰ .F-seqᴰ fᴰ gᴰ , Gᴰ .F-seqᴰ _ _)

-- Weaken a displayed category Dᴰ over Cᴰ
module _ {C : Category ℓC ℓC'}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ')
  where

  open Categoryᴰ
  private
    module Dᴰ = Categoryᴰ Dᴰ

  weakenᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ'
  weakenᴰ .ob[_] (x , _) = Dᴰ.ob[ x ]
  weakenᴰ .Hom[_][_,_] (f , _) = Dᴰ.Hom[ f ][_,_]
  weakenᴰ .idᴰ = Dᴰ.idᴰ
  weakenᴰ ._⋆ᴰ_ = Dᴰ._⋆ᴰ_
  weakenᴰ .⋆IdLᴰ = Dᴰ.⋆IdLᴰ
  weakenᴰ .⋆IdRᴰ = Dᴰ.⋆IdRᴰ
  weakenᴰ .⋆Assocᴰ = Dᴰ.⋆Assocᴰ
  weakenᴰ .isSetHomᴰ = Dᴰ.isSetHomᴰ

