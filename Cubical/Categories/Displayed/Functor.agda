{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

record Functorᴰ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : Functor C D) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') (ℓ-max ℓDᴰ ℓDᴰ'))) where
  no-eta-equality

  open Category
  open Functor F
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  field
    F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F-ob x ]
    F-homᴰ : {x y : C .ob} {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      → Cᴰ [ f ][ xᴰ , yᴰ ] → Dᴰ [ F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]
    F-idᴰ : {x : C .ob} {xᴰ : Cᴰ.ob[ x ]}
      → PathP (λ i → Dᴰ [ F-id i ][ F-obᴰ xᴰ , F-obᴰ xᴰ ] ) (F-homᴰ Cᴰ.idᴰ) Dᴰ.idᴰ
    F-seqᴰ : {x y z : C .ob} {f : C [ x , y ]} {g : C [ y , z ]}
      {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
      (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ [ g ][ yᴰ , zᴰ ])
      → PathP (λ i → Dᴰ [ F-seq f g i ][ F-obᴰ xᴰ , F-obᴰ zᴰ ]) (F-homᴰ (fᴰ Cᴰ.⋆ᴰ gᴰ)) (F-homᴰ fᴰ Dᴰ.⋆ᴰ F-homᴰ gᴰ)

-- Displayed identity functor

module _ where
  open Functorᴰ

  𝟙ᴰ⟨_⟩ : {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') → Functorᴰ 𝟙⟨ C ⟩ Cᴰ Cᴰ
  𝟙ᴰ⟨ Cᴰ ⟩ .F-obᴰ x    = x
  𝟙ᴰ⟨ Cᴰ ⟩ .F-homᴰ f   = f
  𝟙ᴰ⟨ Cᴰ ⟩ .F-idᴰ      = refl
  𝟙ᴰ⟨ Cᴰ ⟩ .F-seqᴰ _ _ = refl

-- Displayed functor composition

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  {F : Functor C D} {G : Functor D E}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'} {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
  (Gᴰ : Functorᴰ G Dᴰ Eᴰ) (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where

  open Functorᴰ
  private
    module Fᴰ = Functorᴰ Fᴰ
    module Gᴰ = Functorᴰ Gᴰ

  funcCompᴰ : Functorᴰ (funcComp G F) Cᴰ Eᴰ
  funcCompᴰ .F-obᴰ = Gᴰ.F-obᴰ ∘ Fᴰ.F-obᴰ
  funcCompᴰ .F-homᴰ = Gᴰ.F-homᴰ ∘ Fᴰ.F-homᴰ
  funcCompᴰ .F-idᴰ = compPathP' {B = Eᴰ [_][ _ , _ ]} (congP (λ _ → Gᴰ.F-homᴰ) Fᴰ.F-idᴰ) Gᴰ.F-idᴰ
  funcCompᴰ .F-seqᴰ _ _ =
    compPathP' {B = Eᴰ [_][ _ , _ ]} (congP (λ _ → Gᴰ.F-homᴰ) (Fᴰ.F-seqᴰ _ _) ) (Gᴰ.F-seqᴰ _ _)
