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
open import Cubical.Categories.Monoidal.Braided

module _ {ℓ ℓ' : Level} (C : Category ℓ ℓ') where
  open Category C
  open Functor

  record SymmMonStr : Type (ℓ-max ℓ ℓ') where
    field
      braidedstr : BraidedStr C

    open BraidedStr braidedstr public

    field
      -- a symmetric monoidal category is just a braided monoidal category
      -- that is as commutative as possible
      B⋆B≡id : ∀ x y → B⟨ y , x ⟩ ⋆ B⟨ x , y ⟩ ≡ id

record SymmetricMonCategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    C : Category ℓ ℓ'
    symmmonstr : SymmMonStr C

  open Category C public
  open SymmMonStr symmmonstr public
