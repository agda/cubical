-- Defines abelian categories
{-# OPTIONS --safe -W ignore #-}

module Cubical.Categories.Abelian.Base where

open import Agda.Primitive using (Level)
open import Cubical.Algebra.AbGroup.Base using (AbGroupStr)
open import Cubical.Categories.Category.Base using (Precategory; _[_,_]; comp')
open import Cubical.Categories.Limits.Base using (isProduct; isCoproduct)
open import Cubical.Categories.Limits.Terminal using (isInitial; isFinal)
open import Cubical.Foundations.Prelude using (Type; ℓ-suc; ℓ-max; _≡_)

private
  variable
    ℓ ℓ' : Level

module _ (C : Precategory ℓ ℓ') where
  open Precategory

  -- Preadditive categories
  record isPreadditive : Type (ℓ-max ℓ (ℓ-suc ℓ')) where --(ℓ-suc (ℓ-max ℓ ℓ')) where
    open AbGroupStr
    -- open Precategory

    field
  --    C : Precategory ℓ ℓ'
      AbEnriched : (x y : ob C) → AbGroupStr (C [ x , y ])
      
      distl : (x y z : ob C) → (f : C [ y , z ]) → (g h : C [ x , y ]) →
        f ∘⟨ C ⟩ (_+_ (AbEnriched x y) g h) ≡ _+_ (AbEnriched x z) (f ∘⟨ C ⟩ g) (f ∘⟨ C ⟩ h)
        -- f ∘ (g + h) ≡ (f ∘ g) + (f ∘ h)

      distr : (x y z : ob C) → (f g : C [ y , z ]) → (h : C [ x , y ]) →
        (_+_ (AbEnriched y z) f g) ∘⟨ C ⟩ h ≡ _+_ (AbEnriched x z) (f ∘⟨ C ⟩ h) (g ∘⟨ C ⟩ h)
        -- (f + g) ∘ h ≡ (f ∘ h) + (g ∘ h)


  -- Zero morphism
  record isZero {x y : ob C} (f : C [ x , y ]) : Type (ℓ-max ℓ ℓ') where
    field
      const : {w : ob C} → (g h : C [ w , x ]) →
        f ∘⟨ C ⟩ g ≡ f ∘⟨ C ⟩ h
      coconst : {z : ob C} → (g h : C [ y , z ]) →
        g ∘⟨ C ⟩ f ≡ h ∘⟨ C ⟩ f


  -- Binary biproducts
  record Biproduct (x y : ob C) : Type (ℓ-max ℓ ℓ') where
    field
      b : ob C
      px : C [ b , x ]
      py : C [ b , y ]
      ix : C [ x , b ]
      iy : C [ y , b ]

      pxix : px ∘⟨ C ⟩ ix ≡ id C x
      pxiy : isZero (px ∘⟨ C ⟩ iy)
      pyix : isZero (py ∘⟨ C ⟩ ix)
      pyiy : py ∘⟨ C ⟩ iy ≡ id C y

      bProd : isProduct {C = C} b px py
      bCopr : isCoproduct {C = C} b ix iy


  -- Additive categories
  record isAdditive : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    -- open AbGroupStr
    -- open Precategory
    -- open Preadditive

    field
      -- C : Precategory ℓ ℓ'
      C-Preadd : isPreadditive

      -- Zero object
      z : ob C
      zInit : isInitial C z
      zFinal : isFinal C z

      -- Binary biproducts
      bp : (x y : ob C) → Biproduct x y