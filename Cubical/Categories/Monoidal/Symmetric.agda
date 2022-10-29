-- Symmetric Monoidal Categories
{-# OPTIONS --safe #-}
module Cubical.Categories.Monoidal.Symmetric where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.BinProduct
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Monoidal.Base

module _ {ℓ ℓ' : Level} (C : Category ℓ ℓ') where
  open Category C
  open Functor

  -- private record to define the functors that describe the braiding
  -- and nice names to define the actual braiding
  private
    record BraidedStr : Type (ℓ-max ℓ ℓ') where
      field
        monstr : MonoidalStr C

      open MonoidalStr monstr public

      [x⊗y] : Functor (C × C) C
      [x⊗y] = ─⊗─

      -- just ─⊗─ but swaps the arguments
      [y⊗x] : Functor (C × C) C
      F-ob  [y⊗x] (x , y) = y ⊗ x
      F-hom [y⊗x] (f , g) = g ⊗ₕ f
      F-id  [y⊗x]         = ─⊗─ .F-id
      F-seq [y⊗x] f g     = ─⊗─ .F-seq (snd f , fst f) (snd g , fst g)

  record SymmMonStr : Type (ℓ-max ℓ ℓ') where
    field
      braidedstr : BraidedStr

    open BraidedStr braidedstr public

    field
      -- the natural isomorphism the performs the braiding
      B : [x⊗y] ≅ᶜ [y⊗x]

    open NatTrans
    open NatIso

    -- nice notation
    B⟨_,_⟩ : (x y : ob) → Hom[ x ⊗ y , y ⊗ x ]
    B⟨ x , y ⟩ = B .trans ⟦ (x , y) ⟧

    field
      -- the required commuting diagrams
      B⋆B≡id : ∀ x y → B⟨ y , x ⟩ ⋆ B⟨ x , y ⟩ ≡ id
      hexagon : ∀ x y z →
        α⁻¹⟨ x , y , z ⟩ ⋆ B⟨ x , y ⊗ z ⟩ ⋆ α⁻¹⟨ y , z , x ⟩
          ≡  B⟨ x , y ⟩ ⊗ₕ id ⋆ α⁻¹⟨ y , x , z ⟩ ⋆ id ⊗ₕ B⟨ x , z ⟩

    open isIso

    -- the inverse for convenience
    B⁻¹⟨_,_⟩ : (x y : ob) → Hom[ y ⊗ x , x ⊗ y ]
    B⁻¹⟨ x , y ⟩ = B .nIso (x , y) .inv

record SymmetricMonCategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    C : Category ℓ ℓ'
    symmmonstr : SymmMonStr C

  open Category C public
  open SymmMonStr symmmonstr public
