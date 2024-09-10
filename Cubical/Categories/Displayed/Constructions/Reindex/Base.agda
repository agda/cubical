{-

   Given any displayed cat and functor to the base

           A
           |
           |
           |
           |
           ↓
   Δ ----→ Γ
       γ


   There is a universal displayed category over Δ equipped with a
   displayed functor

   γ* A ----→ A
     |        |
     |        |
     |        |
     |        |
     ↓        ↓
     Δ -----→ Γ
        γ


   We write γ* A as reindex A γ*

   The universality says that a section

          γ* A
        ↗ |
       /  |
    M /   |
     /    |
    /     ↓
   Θ ---→ Δ
       δ

   is equivalent to a section

          A
        ↗ |
       /  |
      /   |
     /    |
    /     ↓
   Θ ---→ Γ
      δγ

   that factorizes through the universal displayed functor.

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Reindex.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Unit
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Terminal

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where

  private
    module R = HomᴰReasoning Dᴰ
    module C = Category C
    module D = Category D

  open Categoryᴰ Dᴰ
  open Functor F
  open Functorᴰ

  reindex : Categoryᴰ C ℓDᴰ ℓDᴰ'
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

  π : Functorᴰ F reindex Dᴰ
  π .F-obᴰ = λ z → z
  π .F-homᴰ = λ z → z
  π .F-idᴰ = symP (transport-filler _ _)
  π .F-seqᴰ fᴰ gᴰ = symP (transport-filler _ _)

  GlobalSectionReindex→Section : GlobalSection reindex → Section F Dᴰ
  GlobalSectionReindex→Section Fᴰ = compFunctorᴰGlobalSection π Fᴰ

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {B : Category ℓB ℓB'}
  (G : Functor B C)
  (FGᴰ : Section (F ∘F G) Dᴰ)
  where
  private
    module R = HomᴰReasoning Dᴰ
  open Functor
  open Section

  introS : Section G (reindex Dᴰ F)
  introS .F-obᴰ = FGᴰ .F-obᴰ
  introS .F-homᴰ = FGᴰ .F-homᴰ
  introS .F-idᴰ = R.≡[]-rectify (R.≡[]∙ _ _ (FGᴰ .F-idᴰ) (R.reind-filler _ _))
  introS .F-seqᴰ fᴰ gᴰ =
    R.≡[]-rectify (R.≡[]∙ _ _ (FGᴰ .F-seqᴰ fᴰ gᴰ) (R.reind-filler _ _))

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {B : Category ℓB ℓB'} {Bᴰ : Categoryᴰ B ℓBᴰ ℓBᴰ'}
  (G : Functor B C)
  (FGᴰ : Functorᴰ (F ∘F G) Bᴰ Dᴰ)
  where
  introF : Functorᴰ G Bᴰ (reindex Dᴰ F)
  introF = TotalCat.recᴰ _ _ (introS _
    (reindS' (Eq.refl , Eq.refl) (TotalCat.elim FGᴰ)))
