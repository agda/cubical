{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Preorder where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.HLevels

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

record Preorderᴰ (C : Category ℓC ℓC') ℓCᴰ ℓCᴰ' :
  Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))) where
  open Category C
  field
    ob[_] : ob → Type ℓCᴰ
    Hom[_][_,_] : {x y : ob} → Hom[ x , y ] → ob[ x ] → ob[ y ] → Type ℓCᴰ'
    idᴰ : ∀ {x} {p : ob[ x ]} → Hom[ id ][ p , p ]
    _⋆ᴰ_ : ∀ {x y z} {f : Hom[ x , y ]} {g : Hom[ y , z ]} {xᴰ yᴰ zᴰ}
      → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f ⋆ g ][ xᴰ , zᴰ ]
    isPropHomᴰ : ∀ {x y} {f : Hom[ x , y ]} {xᴰ yᴰ} → isProp Hom[ f ][ xᴰ , yᴰ ]

module _
       {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
       (F : Functor C D)
       (Pᴰ : Preorderᴰ C ℓCᴰ ℓCᴰ') (Qᴰ : Preorderᴰ D ℓDᴰ ℓDᴰ')
       where
  open Category
  open Functor
  private
    module Pᴰ = Preorderᴰ Pᴰ
    module Qᴰ = Preorderᴰ Qᴰ
  record Monotoneᴰ : Type ((ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
                           (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') (ℓ-max ℓDᴰ ℓDᴰ')))) where
    field
      F-obᴰ  : {x : C .ob} → Pᴰ.ob[ x ] → Qᴰ.ob[ F .F-ob x ]
      F-homᴰ : {x y : C .ob} {f : C [ x , y ]}
        {xᴰ : Pᴰ.ob[ x ]} {yᴰ : Pᴰ.ob[ y ]}
        → Pᴰ.Hom[ f ][ xᴰ , yᴰ ] → Qᴰ.Hom[ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]

module _ {C : Category ℓC ℓC'} (Pᴰ : Preorderᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  open Preorderᴰ
  Preorderᴰ→Catᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
  Preorderᴰ→Catᴰ = record
    { ob[_] = Pᴰ .ob[_]
    ; Hom[_][_,_] = Pᴰ .Hom[_][_,_]
    ; idᴰ = Pᴰ .idᴰ
    ; _⋆ᴰ_ = Pᴰ ._⋆ᴰ_
    ; ⋆IdLᴰ = λ _ →
      isProp→PathP ((λ i → Pᴰ .isPropHomᴰ {f = ((C .⋆IdL _) i)})) _ _
    ; ⋆IdRᴰ = λ _ →
      isProp→PathP ((λ i → Pᴰ .isPropHomᴰ {f = ((C .⋆IdR _) i)})) _ _
    ; ⋆Assocᴰ = λ _ _ _ →
      isProp→PathP ((λ i → Pᴰ .isPropHomᴰ {f = ((C .⋆Assoc _ _ _) i)})) _ _
    ; isSetHomᴰ = isProp→isSet (Pᴰ .isPropHomᴰ)
    }

  hasPropHomsPreorderᴰ : hasPropHoms Preorderᴰ→Catᴰ
  hasPropHomsPreorderᴰ _ _ _ = Pᴰ .isPropHomᴰ

  open Functor

  Preorderᴰ→FstFaithful : isFaithful (Fst {Cᴰ = Preorderᴰ→Catᴰ})
  Preorderᴰ→FstFaithful x y f g p =
    ΣPathP (p ,
      isProp→PathP (λ i → Pᴰ .isPropHomᴰ {f = p i}) (f .snd) (g .snd))

  module Pᴰ = Preorderᴰ Pᴰ
  record Section  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ')) where
    field
      F-ob : ∀ c → Pᴰ.ob[ c ]
      F-hom : ∀ {c c'} (f : C [ c , c' ]) → Pᴰ.Hom[ f ][ F-ob c , F-ob c' ]

  module _ {D : Category ℓD ℓD'} (F : Functor D C) where
    reindex : Preorderᴰ D ℓCᴰ ℓCᴰ'
    reindex .ob[_] A = Pᴰ .ob[_] (F ⟅ A ⟆)
    reindex .Hom[_][_,_] f P Q = Pᴰ .Hom[_][_,_] (F ⟪ f ⟫) P Q
    reindex .idᴰ {A} {p} =
      transport (λ i → Pᴰ .Hom[_][_,_] (F .F-id (~ i)) p p) (Pᴰ .idᴰ)
    reindex ._⋆ᴰ_ {f = f}{g = g}{xᴰ = xᴰ}{zᴰ = zᴰ} fᴰ gᴰ =
      transport
        (λ i → Pᴰ .Hom[_][_,_] (F .F-seq f g (~ i)) xᴰ zᴰ)
        (Pᴰ ._⋆ᴰ_ fᴰ gᴰ)
    reindex .isPropHomᴰ = Pᴰ .isPropHomᴰ

module _
       {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
       (F : Functor C D)
       (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (Qᴰ : Preorderᴰ D ℓDᴰ ℓDᴰ') where
  open Category
  open Functor
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Qᴰ = Preorderᴰ Qᴰ

  module _
       (F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Qᴰ.ob[ F .F-ob x ])
       (F-homᴰ : {x y : C .ob} {f : C [ x , y ]}
       {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
        → Cᴰ.Hom[ f ][ xᴰ , yᴰ ]
        → Qᴰ.Hom[ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]) where

    mkP→CᴰFunctorᴰ : Functorᴰ F Cᴰ (Preorderᴰ→Catᴰ Qᴰ)
    mkP→CᴰFunctorᴰ = mkFunctorᴰPropHoms (hasPropHomsPreorderᴰ Qᴰ) F-obᴰ F-homᴰ
