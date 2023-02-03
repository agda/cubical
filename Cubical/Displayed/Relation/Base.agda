{-

  Definition of something

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Displayed.Relation.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Adjoint
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients as Quo
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.ZigZag.Base

open Category

private
  variable
    ℓC ℓ→C ℓD ℓ→D ℓR ℓ→R ℓS ℓ→S : Level
    ℓCᴰ ℓ→Cᴰ ℓDᴰ ℓ→Dᴰ ℓRᴰ ℓ→Rᴰ ℓSᴰ ℓ→Sᴰ : Level

open Categoryᴰ

RelCat : (C : Category ℓC ℓ→C) → ∀ ℓR ℓ→R → Type _
RelCat C ℓR ℓ→R = Categoryᴰ (C ×C C) ℓR ℓ→R

RelCatᴰ : {C : Category ℓC ℓ→C} → RelCat C ℓR ℓ→R → Categoryᴰ C ℓCᴰ ℓ→Cᴰ → ∀ ℓS ℓ→S → Type _
RelCatᴰ ℛ-C Cᴰ ℓS ℓ→S = Categoryᴰ (∫C (weakenᴰ ℛ-C (Cᴰ ×Cᴰ Cᴰ))) ℓS ℓ→S

-- Total RelCat of a displayed RelCat
module _ {C : Category ℓC ℓ→C} {ℛ-C : RelCat C ℓR ℓ→R} {Cᴰ : Categoryᴰ C ℓCᴰ ℓ→Cᴰ} {ℓS ℓ→S}
  (ℛ-Cᴰ : RelCatᴰ ℛ-C Cᴰ ℓS ℓ→S)
  where

  private
    module ℛ-C = Categoryᴰ ℛ-C
    module ℛ-Cᴰ = Categoryᴰ ℛ-Cᴰ

  ℛ-∫ : RelCat (∫C Cᴰ) (ℓ-max ℓR ℓS) (ℓ-max ℓ→R ℓ→S)
  ℛ-∫ .ob[_] ((x , xᴰ) , (y , yᴰ)) = Σ[ r ∈ ℛ-C.ob[ x , y ] ] ℛ-Cᴰ.ob[ (_ , r) , xᴰ , yᴰ ]
  ℛ-∫ .Hom[_][_,_] ((f , fᴰ) , (g , gᴰ)) (r , rᴰ) (s , sᴰ) =
    Σ[ h ∈ ℛ-C.Hom[ f , g ][ r , s ] ] ℛ-Cᴰ.Hom[ (_ , h) , fᴰ , gᴰ ][ rᴰ , sᴰ ]
  ℛ-∫ .idᴰ = ℛ-C.idᴰ , ℛ-Cᴰ.idᴰ
  ℛ-∫ ._⋆ᴰ_ (h , hᴰ) (k , kᴰ) = (h ℛ-C.⋆ᴰ k) , (hᴰ ℛ-Cᴰ.⋆ᴰ kᴰ)
  ℛ-∫ .⋆IdLᴰ _ = ΣPathP (ℛ-C.⋆IdLᴰ _ , ℛ-Cᴰ.⋆IdLᴰ _)
  ℛ-∫ .⋆IdRᴰ _ = ΣPathP (ℛ-C.⋆IdRᴰ _ , ℛ-Cᴰ.⋆IdRᴰ _)
  ℛ-∫ .⋆Assocᴰ _ _ _ = ΣPathP (ℛ-C.⋆Assocᴰ _ _ _ , ℛ-Cᴰ.⋆Assocᴰ _ _ _)
  ℛ-∫ .isSetHomᴰ = isSetΣ ℛ-C.isSetHomᴰ (λ _ → ℛ-Cᴰ.isSetHomᴰ)

RelCatFunctor : (C : Category ℓC ℓ→C) (D : Category ℓD ℓ→D)
    (ℛ-C : RelCat C ℓR ℓ→R) (ℛ-D : RelCat D ℓS ℓ→S)
    → Type _
RelCatFunctor _ _ ℛ-C ℛ-D = Functor (∫C ℛ-C) (∫C ℛ-D)

RelCatAdjoint : (C : Category ℓC ℓ→C) (D : Category ℓD ℓ→D)
  (ℛ-C : RelCat C ℓR ℓ→R) (ℛ-D : RelCat D ℓS ℓ→S)
  → RelCatFunctor C D ℛ-C ℛ-D
  → RelCatFunctor D C ℛ-D ℛ-C
  → Type _
RelCatAdjoint _ _ _ _ F G = F UnitCounit.⊣ G

RelCatFunctorᴰ : {C : Category ℓC ℓ→C} {D : Category ℓD ℓ→D}
  {ℛ-C : RelCat C ℓR ℓ→R} {ℛ-D : RelCat D ℓS ℓ→S} (F : RelCatFunctor C D ℛ-C ℛ-D)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓ→Cᴰ) (Dᴰ : Categoryᴰ D ℓDᴰ ℓ→Dᴰ)
  → RelCatᴰ ℛ-C Cᴰ ℓRᴰ ℓ→Rᴰ
  → RelCatᴰ ℛ-D Dᴰ ℓSᴰ ℓ→Sᴰ
  → Type _
RelCatFunctorᴰ {C = C} {D} {ℛ-C} {ℛ-D} F Cᴰ Dᴰ ℛ-Cᴰ ℛ-Dᴰ =
  Functorᴰ F (∫Cᴰ (weakenᴰ ℛ-C (Cᴰ ×Cᴰ Cᴰ)) ℛ-Cᴰ) (∫Cᴰ (weakenᴰ ℛ-D (Dᴰ ×Cᴰ Dᴰ)) ℛ-Dᴰ)

RelCatAdjointᴰ : {C : Category ℓC ℓ→C} {D : Category ℓD ℓ→D}
  {ℛ-C : RelCat C ℓR ℓ→R} {ℛ-D : RelCat D ℓS ℓ→S}
  {F : RelCatFunctor C D ℛ-C ℛ-D} {G : RelCatFunctor D C ℛ-D ℛ-C}
  (A : RelCatAdjoint C D ℛ-C ℛ-D F G)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓ→Cᴰ) (Dᴰ : Categoryᴰ D ℓDᴰ ℓ→Dᴰ)
  (ℛ-Cᴰ : RelCatᴰ ℛ-C Cᴰ ℓRᴰ ℓ→Rᴰ) (ℛ-Dᴰ : RelCatᴰ ℛ-D Dᴰ ℓSᴰ ℓ→Sᴰ)
  → RelCatFunctorᴰ F Cᴰ Dᴰ ℛ-Cᴰ ℛ-Dᴰ
  → RelCatFunctorᴰ G Dᴰ Cᴰ ℛ-Dᴰ ℛ-Cᴰ
  → Type _
RelCatAdjointᴰ A _ _ _ _ Fᴰ Gᴰ = Fᴰ UnitCounitᴰ.⊣[ A ] Gᴰ
