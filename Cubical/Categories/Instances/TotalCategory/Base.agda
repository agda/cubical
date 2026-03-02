module Cubical.Categories.Instances.TotalCategory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor

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
