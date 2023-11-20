{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Terminal

module Cubical.Categories.Displayed.Properties where

private
  variable
    ℓC ℓ'C ℓD ℓ'D ℓCᴰ ℓ'Cᴰ ℓDᴰ ℓ'Dᴰ : Level

module _
  {C : Category ℓC ℓ'C} {D : Category ℓD ℓ'D}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓ'Dᴰ) (F : Functor C D)
  where

  private
    module R = HomᴰReasoning Dᴰ
    module C = Category C
    module D = Category D

  open Categoryᴰ Dᴰ
  open Functor F

  reindex : Categoryᴰ C ℓDᴰ ℓ'Dᴰ
  reindex .Categoryᴰ.ob[_] c = ob[ F-ob c ]
  reindex .Categoryᴰ.Hom[_][_,_] f aᴰ bᴰ = Hom[ F-hom f ][ aᴰ , bᴰ ]
  reindex .Categoryᴰ.idᴰ = R.reind (sym F-id) idᴰ
  reindex .Categoryᴰ._⋆ᴰ_ fᴰ gᴰ = R.reind (sym $ F-seq _ _) (fᴰ ⋆ᴰ gᴰ)
  reindex .Categoryᴰ.⋆IdLᴰ fᴰ = R.≡[]-rectify $
    R.reind-filler-sym (F-seq _ _) _
      R.[ _ ]∙[ _ ]
    (R.reind-filler-sym F-id idᴰ R.[ _ ]⋆[ refl ] refl)
      R.[ _ ]∙[ _ ]
    ⋆IdLᴰ fᴰ
  reindex .Categoryᴰ.⋆IdRᴰ fᴰ = R.≡[]-rectify $
    R.reind-filler-sym (F-seq _ _) _
      R.[ _ ]∙[ _ ]
    (refl R.[ refl ]⋆[ _ ] R.reind-filler-sym F-id idᴰ)
      R.[ _ ]∙[ _ ]
    ⋆IdRᴰ fᴰ
  reindex .Categoryᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ = R.≡[]-rectify $
    R.reind-filler-sym (F-seq _ _) _
      R.[ _ ]∙[ _ ]
    (R.reind-filler-sym (F-seq _ _) _ R.[ _ ]⋆[ refl ] refl)
      R.[ _ ]∙[ _ ]
    ⋆Assocᴰ fᴰ gᴰ hᴰ
      R.[ _ ]∙[ _ ]
    (refl R.[ refl ]⋆[ _ ] R.reind-filler (sym $ F-seq _ _) _)
      R.[ _ ]∙[ _ ]
    R.reind-filler (sym $ F-seq _ _) _
  reindex .Categoryᴰ.isSetHomᴰ = isSetHomᴰ


module _ {ℓ* : Level} (Cᴰ : Categoryᴰ (TerminalCategory {ℓ*}) ℓCᴰ ℓ'Cᴰ) where
  open Categoryᴰ Cᴰ
  open Category hiding (_∘_)

  DispOverTerminal→Category : Category ℓCᴰ ℓ'Cᴰ
  DispOverTerminal→Category .ob = ob[ tt* ]
  DispOverTerminal→Category .Hom[_,_] = Hom[ refl ][_,_]
  DispOverTerminal→Category .id = idᴰ
  DispOverTerminal→Category ._⋆_ = _⋆ᴰ_
  DispOverTerminal→Category .⋆IdL = ⋆IdLᴰ
  DispOverTerminal→Category .⋆IdR = ⋆IdRᴰ
  DispOverTerminal→Category .⋆Assoc = ⋆Assocᴰ
  DispOverTerminal→Category .isSetHom = isSetHomᴰ

module _ (C : Category ℓC ℓ'C) where
  open Categoryᴰ
  open Category C hiding (_∘_)

  Category→DispOverTerminal : {ℓ* : Level} → Categoryᴰ (TerminalCategory {ℓ*}) ℓC ℓ'C
  Category→DispOverTerminal .ob[_] _ = ob
  Category→DispOverTerminal .Hom[_][_,_] _ = Hom[_,_]
  Category→DispOverTerminal .idᴰ = id
  Category→DispOverTerminal ._⋆ᴰ_ = _⋆_
  Category→DispOverTerminal .⋆IdLᴰ = ⋆IdL
  Category→DispOverTerminal .⋆IdRᴰ = ⋆IdR
  Category→DispOverTerminal .⋆Assocᴰ = ⋆Assoc
  Category→DispOverTerminal .isSetHomᴰ = isSetHom

module _ {C : Category ℓC ℓ'C} (Cᴰ : Categoryᴰ C ℓCᴰ ℓ'Cᴰ) where
  open Category C
  open Categoryᴰ Cᴰ
  VerticalCategory : ob → Category ℓCᴰ ℓ'Cᴰ
  VerticalCategory c = DispOverTerminal→Category (reindex Cᴰ (FunctorFromTerminal {ℓ* = ℓ-zero} c))
