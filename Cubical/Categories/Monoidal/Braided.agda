-- Braided Monoidal Categories
-- as defined here:
-- https://ncatlab.org/nlab/show/braided+monoidal+category
{-# OPTIONS --safe #-}
module Cubical.Categories.Monoidal.Braided where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Monoidal.Base

module _ {ℓ ℓ' : Level} (C : Category ℓ ℓ') where
  open Category C
  open Functor

  record BraidedStr : Type (ℓ-max ℓ ℓ') where
    field
      monstr : MonoidalStr C

    open MonoidalStr monstr public

    -- private names to make the braiding look nice
    private
      [x⊗y] : Functor (C × C) C
      [x⊗y] = ─⊗─

      -- just ─⊗─ but swaps the arguments
      [y⊗x] : Functor (C × C) C
      [y⊗x] = ─⊗─ ∘F ×C-comm C C

    field
      -- the braiding
      B : [x⊗y] ≅ᶜ [y⊗x]

    open NatTrans
    open NatIso

    -- nice notation
    B⟨_,_⟩ : (x y : ob) → Hom[ x ⊗ y , y ⊗ x ]
    B⟨ x , y ⟩ = B .trans ⟦ (x , y) ⟧

    field
      -- the hexagon identities
      hexagon : ∀ x y z →
        α⟨ x , y , z ⟩ ⋆ B⟨ x ⊗ y , z ⟩ ⋆ α⟨ z , x , y ⟩
          ≡  id ⊗ₕ B⟨ y , z ⟩ ⋆ α⟨ x , z , y ⟩ ⋆ B⟨ x , z ⟩ ⊗ₕ id
      hexagon⁻¹ : ∀ x y z →
        α⁻¹⟨ x , y , z ⟩ ⋆ B⟨ x , y ⊗ z ⟩ ⋆ α⁻¹⟨ y , z , x ⟩
          ≡  B⟨ x , y ⟩ ⊗ₕ id ⋆ α⁻¹⟨ y , x , z ⟩ ⋆ id ⊗ₕ B⟨ x , z ⟩

    open isIso

    -- the inverse for convenience
    B⁻¹⟨_,_⟩ : (x y : ob) → Hom[ y ⊗ x , x ⊗ y ]
    B⁻¹⟨ x , y ⟩ = B .nIso (x , y) .inv

record BraidedMonCategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    C : Category ℓ ℓ'
    braidedstr : BraidedStr C

  open Category C public
  open BraidedStr braidedstr public
