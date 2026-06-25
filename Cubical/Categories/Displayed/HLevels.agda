{-- This file contains some utilities for reasoning
 -- about the HLevels of morphisms in displayed categories.
 --}
module Cubical.Categories.Displayed.HLevels where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base

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

  hasPropHoms→isPropCatIsoᴰ : hasPropHoms
    → ∀ {c}{c'}{f : CatIso C c c'}{cᴰ : Cᴰ.ob[ c ]}{cᴰ' : Cᴰ.ob[ c' ]}
    → isProp (CatIsoᴰ Cᴰ f cᴰ cᴰ')
  hasPropHoms→isPropCatIsoᴰ propHoms {c} {c'} {f} {cᴰ} {cᴰ'} =
    isPropΣ (propHoms (f .fst) cᴰ cᴰ') (λ _ →
    isPropRetract
      (isIsoᴰIsoΣ Cᴰ .Iso.fun) (isIsoᴰIsoΣ Cᴰ .Iso.inv) (isIsoᴰIsoΣ Cᴰ .Iso.ret)
      (isPropΣ (propHoms (f .snd .isIso.inv) cᴰ' cᴰ) (λ _ → isProp×
        (isOfHLevelPathP' 1 Cᴰ.isSetHomᴰ _ _)
        (isOfHLevelPathP' 1 Cᴰ.isSetHomᴰ _ _))))

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
module _
       {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
       {F : Functor C D}
       {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Category
  open Functor
  private
    module Dᴰ = Categoryᴰ Dᴰ
  mkPropHomsSection :
    (propHoms : hasPropHoms Dᴰ)
      → (F-obᴰ  : (x : C .ob) → Dᴰ.ob[ F .F-ob x ])
      → (F-homᴰ : {x y : C .ob}
        (f : C [ x , y ]) → Dᴰ [ F .F-hom f ][ F-obᴰ x , F-obᴰ y ])
      → Section F Dᴰ
  mkPropHomsSection propHoms F-obᴰ F-homᴰ .Section.F-obᴰ = F-obᴰ
  mkPropHomsSection propHoms F-obᴰ F-homᴰ .Section.F-homᴰ = F-homᴰ
  mkPropHomsSection propHoms F-obᴰ F-homᴰ .Section.F-idᴰ =
    isProp→PathP (λ i → propHoms _ _ _) _ _
  mkPropHomsSection propHoms F-obᴰ F-homᴰ .Section.F-seqᴰ _ _ =
    isProp→PathP (λ i → propHoms _ _ _) _ _

  mkContrHomsSection :
    (contrHoms : hasContrHoms Dᴰ)
      → (F-obᴰ  : (x : C .ob) → Dᴰ.ob[ F .F-ob x ])
      → Section F Dᴰ
  mkContrHomsSection contrHoms F-obᴰ = mkPropHomsSection
    (hasContrHoms→hasPropHoms Dᴰ contrHoms)
    F-obᴰ
      λ {x}{y} f → contrHoms (F .F-hom f) (F-obᴰ x) (F-obᴰ y) .fst

  module _ {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
    private
      module Cᴰ = Categoryᴰ Cᴰ
    -- Alternate version: maybe Dᴰ.Hom[_][_,_] isn't always
    -- contractible, but it is in the image of F-obᴰ
    mkContrHomsFunctor'
      : (F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ])
      → (F-homᴰ : {x y : C .ob}
        {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      → Cᴰ [ f ][ xᴰ , yᴰ ]
      → isContr (Dᴰ [ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]))
      → Functorᴰ F Cᴰ Dᴰ
    mkContrHomsFunctor' F-obᴰ F-homᴰ .Functorᴰ.F-obᴰ = F-obᴰ
    mkContrHomsFunctor' F-obᴰ F-homᴰ .Functorᴰ.F-homᴰ fᴰ = F-homᴰ fᴰ .fst
    mkContrHomsFunctor' F-obᴰ F-homᴰ .Functorᴰ.F-idᴰ =
      symP (toPathP (isProp→PathP (λ i → isContr→isProp (F-homᴰ Cᴰ.idᴰ)) _ _))
    mkContrHomsFunctor' F-obᴰ F-homᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ =
      symP (toPathP (isProp→PathP
        (λ i → isContr→isProp (F-homᴰ (fᴰ Cᴰ.⋆ᴰ gᴰ))) _ _))
