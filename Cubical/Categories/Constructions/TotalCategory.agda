{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.TotalCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Terminal

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

-- Total category of a displayed category
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  open Category
  open Categoryᴰ Cᴰ
  private
    module C = Category C

  ∫C : Category (ℓ-max ℓC ℓCᴰ) (ℓ-max ℓC' ℓCᴰ')
  ∫C .ob = Σ _ ob[_]
  ∫C .Hom[_,_] (_ , xᴰ) (_ , yᴰ) = Σ _ Hom[_][ xᴰ , yᴰ ]
  ∫C .id = _ , idᴰ
  ∫C ._⋆_ (_ , fᴰ) (_ , gᴰ) = _ , fᴰ ⋆ᴰ gᴰ
  ∫C .⋆IdL _ = ΣPathP (_ , ⋆IdLᴰ _)
  ∫C .⋆IdR _ = ΣPathP (_ , ⋆IdRᴰ _)
  ∫C .⋆Assoc _ _ _ = ΣPathP (_ , ⋆Assocᴰ _ _ _)
  ∫C .isSetHom = isSetΣ C.isSetHom (λ _ → isSetHomᴰ)

-- Total functor of a displayed functor
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : Functor C D} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where

  open Functor
  private
    module Fᴰ = Functorᴰ Fᴰ

  ∫F : Functor (∫C Cᴰ) (∫C Dᴰ)
  ∫F .F-ob (x , xᴰ) = _ , Fᴰ.F-obᴰ xᴰ
  ∫F .F-hom (_ , fᴰ) = _ , Fᴰ.F-homᴰ fᴰ
  ∫F .F-id = ΣPathP (_ , Fᴰ.F-idᴰ)
  ∫F .F-seq _ _ = ΣPathP (_ , (Fᴰ.F-seqᴰ _ _))

-- Projections out of the total category
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  open Functor
  open Functorᴰ

  Fst : Functor (∫C Cᴰ) C
  Fst .F-ob = fst
  Fst .F-hom = fst
  Fst .F-id = refl
  Fst .F-seq =
    λ f g → cong {x = f ⋆⟨ ∫C Cᴰ ⟩ g} fst refl

  -- Functor into the total category
  module _ {D : Category ℓD ℓD'}
           (F : Functor D C)
           (Fᴰ : Functorᴰ F (Unitᴰ D) Cᴰ)
           where
    intro : Functor D (∫C Cᴰ)
    intro .F-ob d = F ⟅ d ⟆ , Fᴰ .F-obᴰ _
    intro .F-hom f = (F ⟪ f ⟫) , (Fᴰ .F-homᴰ _)
    intro .F-id = ΣPathP (F .F-id , Fᴰ .F-idᴰ)
    intro .F-seq f g = ΣPathP (F .F-seq f g , Fᴰ .F-seqᴰ _ _)
