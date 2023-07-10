{-
  Definition of a natural transformation displayed over another natural transformation.
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.NaturalTransformation where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where

  record NatTransᴰ
    {F : Functor C D} {G : Functor C D}
    (α : NatTrans F G)
    {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Gᴰ : Functorᴰ G Cᴰ Dᴰ)
    : Type (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ (ℓ-max ℓCᴰ' ℓDᴰ')))) where

    open Category
    open NatTrans α
    open Functorᴰ
    private
      module Cᴰ = Categoryᴰ Cᴰ
      module Dᴰ = Categoryᴰ Dᴰ

    field
      -- components of the natural transformation
      N-obᴰ : {x : C .ob} (xᴰ : Cᴰ.ob[ x ]) → Dᴰ [ N-ob x ][ Fᴰ .F-obᴰ xᴰ , Gᴰ .F-obᴰ xᴰ ]
      -- naturality condition
      N-homᴰ : {x y : C .ob} {f : C [ x , y ]}
        {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ])
        → PathP (λ i → Dᴰ [ N-hom f i ][ Fᴰ .F-obᴰ xᴰ , Gᴰ .F-obᴰ yᴰ ])
            (Fᴰ .F-homᴰ fᴰ Dᴰ.⋆ᴰ N-obᴰ yᴰ) (N-obᴰ xᴰ Dᴰ.⋆ᴰ Gᴰ .F-homᴰ fᴰ)

  open NatTrans
  open NatTransᴰ

  module _ {F G H : Functor C D} {α : NatTrans F G} {β : NatTrans G H}
    {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    {Fᴰ : Functorᴰ F Cᴰ Dᴰ} {Gᴰ : Functorᴰ G Cᴰ Dᴰ} {Hᴰ : Functorᴰ H Cᴰ Dᴰ}
    where

    private
      module Dᴰ = Categoryᴰ Dᴰ
      module Fᴰ = Functorᴰ Fᴰ
      module Hᴰ = Functorᴰ Hᴰ

    -- vertical sequencing
    seqTransᴰ : NatTransᴰ α Fᴰ Gᴰ → NatTransᴰ β Gᴰ Hᴰ → NatTransᴰ (seqTrans α β) Fᴰ Hᴰ
    seqTransᴰ αᴰ βᴰ .N-obᴰ xᴰ = αᴰ .N-obᴰ xᴰ Dᴰ.⋆ᴰ βᴰ .N-obᴰ xᴰ
    seqTransᴰ αᴰ βᴰ .N-homᴰ {xᴰ = xᴰ} {yᴰ = yᴰ} fᴰ =
      compPathP' {B = B} (symP (Dᴰ.⋆Assocᴰ _ _ _))
        (compPathP' {B = B} (λ i → (αᴰ .N-homᴰ fᴰ i) Dᴰ.⋆ᴰ (βᴰ .N-obᴰ _))
          (compPathP' {B = B} (Dᴰ.⋆Assocᴰ _ _ _)
            (compPathP' {B = B} (λ i → (αᴰ .N-obᴰ _) Dᴰ.⋆ᴰ (βᴰ .N-homᴰ fᴰ i))
              (compPathP' {B = B} (symP (Dᴰ.⋆Assocᴰ _ _ _))
                refl)))) -- extra refl at the end to match equational reasoning in seqTrans
      where
      B = Dᴰ [_][ Fᴰ.F-obᴰ xᴰ , Hᴰ.F-obᴰ yᴰ ]
