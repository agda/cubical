module Cubical.Categories.Displayed.Weaken where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.TotalCategory

private
  variable
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

-- Display a category D over C
module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  open Category
  open Categoryᴰ
  weaken : Categoryᴰ C ℓD ℓD'
  weaken .ob[_] x = D .ob
  weaken .Hom[_][_,_] f d d' = D [ d , d' ]
  weaken .idᴰ = D .id
  weaken ._⋆ᴰ_ = D ._⋆_
  weaken .⋆IdLᴰ = D .⋆IdL
  weaken .⋆IdRᴰ = D .⋆IdR
  weaken .⋆Assocᴰ = D .⋆Assoc
  weaken .isSetHomᴰ = D .isSetHom

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
