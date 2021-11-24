-- The (pre)category of (small) categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Categories where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Category.Precategory
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Foundations.Prelude


module _ (ℓ ℓ' : Level) where
  open Precategory

  Cat : Precategory (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  Cat .ob = Category ℓ ℓ'
  Cat .Hom[_,_] = Functor
  Cat .id = 𝟙⟨ _ ⟩
  Cat ._⋆_ G H = H ∘F G
  Cat .⋆IdL _ = F-lUnit
  Cat .⋆IdR _ = F-rUnit
  Cat .⋆Assoc _ _ _ = F-assoc

-- TODO: what is required for Functor C D to be a set?
