-- Defines abelian categories
{-# OPTIONS --safe -W ignore #-}

module Cubical.Categories.Abelian.Base where

open import Agda.Primitive using (Level)
open import Cubical.Algebra.AbGroup.Base using (AbGroupStr)
open import Cubical.Categories.Category.Base using (Precategory; _[_,_]; comp')
open import Cubical.Categories.Limits.Terminal using (isInitial; isFinal)
open import Cubical.Foundations.Prelude using (Type; ℓ-suc; ℓ-max; _≡_)


private
  variable
    ℓ ℓ' : Level

open Precategory


-- Preadditive categories
record isPreadditive (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ (ℓ-suc ℓ')) where --(ℓ-suc (ℓ-max ℓ ℓ')) where
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


-- Binary biproducts
record isBiproduct {C : Precategory ℓ ℓ'} (x y : ob C) : Type where


-- Additive categories
record isAdditive (C : Precategory ℓ ℓ') : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  -- open AbGroupStr
  -- open Precategory
  -- open Preadditive

  field
    -- C : Precategory ℓ ℓ'
    C-Preadd : isPreadditive C

    -- Zero object
    z : ob C
    zInit : isInitial C z
    zFinal : isFinal C z

    -- Binary biproducts
