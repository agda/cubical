{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.TotalCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Constructions.TotalCategory hiding (intro)

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

-- Displayed total category, i.e. Σ for displayed categories
--
-- The ordinary total category (∫C Cᴰ) has as objects
-- pairs (x, xᴰ) where x is an object of C and xᴰ is an object of Cᴰ over x.
--
-- Whereas if we had a category Dᴰ displayed over (∫C Cᴰ),
-- and a category Cᴰ displayed over C, then the
-- displayed total category (∫Cᴰ Cᴰ Dᴰ) likewise has pairs
-- as displayed objects.
--
-- In the displayed total category, we have objects (xᴰ, yᴰ) displayed
-- over x, where x is an object of C, xᴰ an object in Cᴰ displayed over x,
-- and yᴰ is an object of Dᴰ over (x, xᴰ).
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
  ∫Cᴰ .Hom[_][_,_] f (_ , zᴰ) (_ , wᴰ) =
    Σ[ fᴰ ∈ Cᴰ.Hom[ f ][ _ , _ ] ] Dᴰ.Hom[ f , fᴰ ][ zᴰ , wᴰ ]
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
