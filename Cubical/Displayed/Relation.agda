{-

  Definition of something

-}
{-# OPTIONS --safe #-}
module Cubical.Displayed.Relation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Total
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients as Quo
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.ZigZag.Base

open Category

private
  variable
    ℓC ℓ→C ℓD ℓ→D ℓR ℓ→R : Level
    ℓC₀ ℓ→C₀ ℓD₀ ℓ→D₀ ℓR₀ ℓ→R₀ : Level
    ℓC₁ ℓ→C₁ ℓD₁ ℓ→D₁ ℓR₁ ℓ→R₁ : Level

open DisplayedCat

RelCat : (C : Category ℓC ℓ→C) → ∀ ℓR ℓ→R → Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓ→C) (ℓ-max ℓR ℓ→R)))
RelCat C ℓR ℓ→R = DisplayedCat (C ×C C) ℓR ℓ→R

DRelCat : {C : Category ℓC ℓ→C} → RelCat C ℓR ℓ→R → DisplayedCat C ℓD ℓ→D → ∀ ℓS ℓ→S → Type _
DRelCat ℛ-C D ℓS ℓ→S = DisplayedCat (∫ (ℛ-C ×D (D ×CD D))) ℓS ℓ→S

module _ {C : Category ℓC ℓ→C} {ℛ-C : RelCat C ℓR ℓ→R} {D : DisplayedCat C ℓD ℓ→D} {ℓS ℓ→S}
  (ℛ-D : DRelCat ℛ-C D ℓS ℓ→S)
  where

  private
    module C = DisplayedCat ℛ-C
    module D = DisplayedCat ℛ-D

  ℛ-∫ : RelCat (∫ D) (ℓ-max ℓR ℓS) (ℓ-max ℓ→R ℓ→S)
  ℛ-∫ .ob[_] ((x , xᴰ) , (y , yᴰ)) = Σ[ r ∈ C.ob[ x , y ] ] D.ob[ (x , y) , r , xᴰ , yᴰ ]
  ℛ-∫ .Hom[_][_,_] ((f , fᴰ) , (g , gᴰ)) (r , rᴰ) (s , sᴰ) =
    Σ[ h ∈ C.Hom[ f , g ][ r , s ] ] D.Hom[ (f , g) , h , fᴰ , gᴰ ][ rᴰ , sᴰ ]
  ℛ-∫ .idᴰ = C.idᴰ , D.idᴰ
  ℛ-∫ ._⋆ᴰ_ (h , hᴰ) (k , kᴰ) = (h C.⋆ᴰ k) , (hᴰ D.⋆ᴰ kᴰ)
  ℛ-∫ .⋆IdLᴰ _ = ΣPathP (C.⋆IdLᴰ _ , D.⋆IdLᴰ _)
  ℛ-∫ .⋆IdRᴰ _ = ΣPathP (C.⋆IdRᴰ _ , D.⋆IdRᴰ _)
  ℛ-∫ .⋆Assocᴰ _ _ _ = ΣPathP (C.⋆Assocᴰ _ _ _ , D.⋆Assocᴰ _ _ _)
  ℛ-∫ .isSetHomᴰ = isSetΣ C.isSetHomᴰ (λ _ → D.isSetHomᴰ)

RelCatFunctor : (C₀ : Category ℓC₀ ℓ→C₀) (C₁ : Category ℓC₁ ℓ→C₁)
    (ℛ-C₀ : RelCat C₀ ℓR₀ ℓ→R₀) (ℛ-C₁ : RelCat C₁ ℓR₁ ℓ→R₁)
    → Type (ℓ-max (ℓ-max (ℓ-max ℓC₀ ℓ→C₀) (ℓ-max ℓC₁ ℓ→C₁)) (ℓ-max (ℓ-max ℓR₀ ℓ→R₀) (ℓ-max ℓR₁ ℓ→R₁)))
RelCatFunctor _ _ ℛ-C₀ ℛ-C₁ = Functor (∫ ℛ-C₀) (∫ ℛ-C₁)

RelCatAdj : (C₀ : Category ℓC₀ ℓ→C₀) (C₁ : Category ℓC₁ ℓ→C₁)
  (ℛ-C₀ : RelCat C₀ ℓR₀ ℓ→R₀) (ℛ-C₁ : RelCat C₁ ℓR₁ ℓ→R₁)
  → RelCatFunctor C₀ C₁ ℛ-C₀ ℛ-C₁
  → RelCatFunctor C₁ C₀ ℛ-C₁ ℛ-C₀
  → Type (ℓ-max (ℓ-max (ℓ-max ℓC₀ ℓ→C₀) (ℓ-max ℓC₁ ℓ→C₁)) (ℓ-max (ℓ-max ℓR₀ ℓ→R₀) (ℓ-max ℓR₁ ℓ→R₁)))
RelCatAdj _ _ _ _ F G = F UnitCounit.⊣ G
