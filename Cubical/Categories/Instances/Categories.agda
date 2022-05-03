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

  CatPrecategory : Precategory (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  CatPrecategory .ob = Category ℓ ℓ'
  CatPrecategory .Hom[_,_] = Functor
  CatPrecategory .id = 𝟙⟨ _ ⟩
  CatPrecategory ._⋆_ G H = H ∘F G
  CatPrecategory .⋆IdL _ = F-lUnit
  CatPrecategory .⋆IdR _ = F-rUnit
  CatPrecategory .⋆Assoc _ _ _ = F-assoc

-- TODO: what is required for Functor C D to be a set?
