{-
  Weaken a category to be a displayed category.
-}
--
module Cubical.Categories.Displayed.Constructions.Weaken.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Constructions.TotalCategory as TC
  hiding (intro)

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  open Category
  weaken : Categoryᴰ C ℓD ℓD'
  weaken .ob[_] x = D .ob
  weaken .Hom[_][_,_] f d d' = D [ d , d' ]
  weaken .idᴰ = D .id
  weaken ._⋆ᴰ_ = D ._⋆_
  weaken .⋆IdLᴰ = D .⋆IdL
  weaken .⋆IdRᴰ = D .⋆IdR
  weaken .⋆Assocᴰ = D .⋆Assoc
  weaken .isSetHomᴰ = D .isSetHom

  open Functor
  weakenΠ : Functor (∫C weaken) D
  weakenΠ .F-ob = snd
  weakenΠ .F-hom = snd
  weakenΠ .F-id = refl
  weakenΠ .F-seq _ _ = refl

  ∫weaken→×C : Functor (∫C weaken) (C ×C D)
  ∫weaken→×C = TC.Fst ,F weakenΠ

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {E : Category ℓE ℓE'}
         (F : Functor E C)
         (G : Functor E D)
         where
  open Category
  open Functor
  open Section
  introS : Section F (weaken C D)
  introS .F-obᴰ x = G .F-ob x
  introS .F-homᴰ f = G .F-hom f
  introS .F-idᴰ = G .F-id
  introS .F-seqᴰ _ _ = G .F-seq _ _

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {E : Category ℓE ℓE'}
         {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
         (F : Functor E C)
         (G : Functor E D)
         where
  open Category
  open Functor
  open Functorᴰ
  introF : Functorᴰ F Eᴰ (weaken C D)
  introF .F-obᴰ {x} _ = G .F-ob x
  introF .F-homᴰ {x} {y} {f} {xᴰ} {yᴰ} _ = G .F-hom f
  introF .F-idᴰ = G .F-id
  introF .F-seqᴰ _ _ = G .F-seq _ _

introS⁻ : {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {E : Category ℓE ℓE'}
         {F : Functor E C}
       → Section F (weaken C D)
       → Functor E D
introS⁻ {C = C}{D = D}{F = F} Fᴰ =
  weakenΠ C D ∘F TC.intro F Fᴰ

-- TODO: introS/introS⁻ is an Iso

module _ {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} where
  open Functor
  open Functorᴰ

  weakenF : {D : Category ℓD ℓD'} {E : Category ℓE ℓE'} {F : Functor B C}
          → (G : Functor D E)
          → Functorᴰ F (weaken B D) (weaken C E)
  weakenF G .F-obᴰ = G .F-ob
  weakenF G .F-homᴰ = G .F-hom
  weakenF G .F-idᴰ = G .F-id
  weakenF G .F-seqᴰ = G .F-seq

