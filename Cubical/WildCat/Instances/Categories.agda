-- The wild category of (small) categories
{-# OPTIONS --safe #-}

module Cubical.WildCat.Instances.Categories where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties

open import Cubical.WildCat.Base

module _ (ℓ ℓ' : Level) where
  open WildCat

  CatWildCat : WildCat (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  CatWildCat .ob = Category ℓ ℓ'
  CatWildCat .Hom[_,_] = Functor
  CatWildCat .id = 𝟙⟨ _ ⟩
  CatWildCat ._⋆_ G H = H ∘F G
  CatWildCat .⋆IdL _ = F-lUnit
  CatWildCat .⋆IdR _ = F-rUnit
  CatWildCat .⋆Assoc _ _ _ = F-assoc

-- TODO: what is required for Functor C D to be a set?
