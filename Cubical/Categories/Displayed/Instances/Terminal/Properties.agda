module Cubical.Categories.Displayed.Instances.Terminal.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Terminal.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Categoryᴰ
open Functorᴰ
open Section

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         {F : Functor C D}
         where
  recᴰ : (s : Section F Dᴰ) → Functorᴰ F (Unitᴰ C) Dᴰ
  recᴰ s .F-obᴰ {x} _      = s .F-obᴰ x
  recᴰ s .F-homᴰ {f = f} _ = s .F-homᴰ f
  recᴰ s .F-idᴰ      = s .F-idᴰ
  recᴰ s .F-seqᴰ _ _ = s .F-seqᴰ _ _

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         (F : Functor C D) where
  introF : Functorᴰ F Cᴰ (Unitᴰ D)
  introF .F-obᴰ = λ _ → tt
  introF .F-homᴰ = λ _ → tt
  introF .F-idᴰ = refl
  introF .F-seqᴰ _ _ = refl
