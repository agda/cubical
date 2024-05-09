{-# OPTIONS --safe #-}
{-- This file contains some utilities for reasoning
 -- about the HLevels of morphisms in displayed categories.
 --}
module Cubical.Categories.Displayed.HLevels where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  private
    module Cᴰ = Categoryᴰ Cᴰ

  hasContrHoms : Type _
  hasContrHoms =
    ∀ {c c' : C .ob}(f : C [ c , c' ])(cᴰ : Cᴰ.ob[ c ])(cᴰ' : Cᴰ.ob[ c' ])
      → isContr Cᴰ.Hom[ f ][ cᴰ , cᴰ' ]

  hasPropHoms : Type _
  hasPropHoms =
    ∀ {c c' : C .ob}(f : C [ c , c' ])(cᴰ : Cᴰ.ob[ c ])(cᴰ' : Cᴰ.ob[ c' ])
      → isProp Cᴰ.Hom[ f ][ cᴰ , cᴰ' ]

  hasContrHoms→hasPropHoms : hasContrHoms → hasPropHoms
  hasContrHoms→hasPropHoms contrHoms =
    λ f cᴰ cᴰ' → isContr→isProp (contrHoms f cᴰ cᴰ')

module _
       {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
       {F : Functor C D}
       {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
       {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Category
  open Functor
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  module _
    (propHoms : hasPropHoms Dᴰ)
    where

    mkPropHomsFunctor :
        (F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ])
        → (F-homᴰ : {x y : C .ob}
          {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
          → Cᴰ [ f ][ xᴰ , yᴰ ] → Dᴰ [ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ])
        → Functorᴰ F Cᴰ Dᴰ
    mkPropHomsFunctor F-obᴰ F-homᴰ .Functorᴰ.F-obᴰ = F-obᴰ
    mkPropHomsFunctor F-obᴰ F-homᴰ .Functorᴰ.F-homᴰ = F-homᴰ
    mkPropHomsFunctor F-obᴰ F-homᴰ .Functorᴰ.F-idᴰ =
      isProp→PathP (λ i → propHoms _ _ _) _ _
    mkPropHomsFunctor F-obᴰ F-homᴰ .Functorᴰ.F-seqᴰ _ _ =
      isProp→PathP (λ i → propHoms _ _ _) _ _

  module _
    (contrHoms : hasContrHoms Dᴰ)
    where

    mkContrHomsFunctor :  (F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ])
             → Functorᴰ F Cᴰ Dᴰ
    mkContrHomsFunctor F-obᴰ =
      mkPropHomsFunctor (hasContrHoms→hasPropHoms Dᴰ contrHoms) F-obᴰ
      λ _ → contrHoms _ _ _ .fst
