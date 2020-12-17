{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

record Functor (C : Precategory ℓC ℓC') (D : Precategory ℓD ℓD') : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  no-eta-equality
  open Precategory

  field
    F-ob : C .ob → D .ob
    F-hom : {x y : C .ob} → C [ x , y ] → D [(F-ob x) , (F-ob y)]
    F-id : {x : C .ob} → F-hom (C .id x) ≡ D .id (F-ob x)
    F-seq : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ]) → F-hom (f ⋆⟨ C ⟩ g) ≡ (F-hom f) ⋆⟨ D ⟩ (F-hom g)

  isFull = (x y : _) (F[f] : D [(F-ob x) , (F-ob y)]) → ∃ (C [ x , y ]) (λ f → F-hom f ≡ F[f])
  isFaithful = (x y : _) (f g : C [ x , y ]) → F-hom f ≡ F-hom g → f ≡ g


-- Functor results

module _ (C : Precategory ℓC ℓC') (D : Precategory ℓC ℓC') (F : Functor C D ) where
  open Precategory
  open Functor F

  open CatIso

  -- functors preserve isomorphisms
  preserveIsosF : ∀ {x y : C .ob} → CatIso {C = C} x y → CatIso {C = D} (F-ob x) (F-ob y)
  preserveIsosF {x} {y} (catiso f f⁻¹ sec' ret') =
    catiso
      g g⁻¹
      -- sec
      ( (g⁻¹ ⋆⟨ D ⟩ g)
      ≡⟨ sym (F-seq f⁻¹ f) ⟩
        F-hom (f⁻¹ ⋆⟨ C ⟩ f)
      ≡⟨ cong F-hom sec' ⟩
        F-hom (C .id y)
      ≡⟨ F-id ⟩
        D .id y'
      ∎ )
      -- ret
      ( (g ⋆⟨ D ⟩ g⁻¹)
        ≡⟨ sym (F-seq f f⁻¹) ⟩
      F-hom (f ⋆⟨ C ⟩ f⁻¹)
        ≡⟨ cong F-hom ret' ⟩
      F-hom (C .id x)
      ≡⟨ F-id ⟩
        D .id x'
      ∎ )

      where
        x' : D .ob
        x' = F-ob x
        y' : D .ob
        y' = F-ob y

        g : D [ x' , y' ]
        g = F-hom f
        g⁻¹ : D [ y' , x' ]
        g⁻¹ = F-hom f⁻¹
