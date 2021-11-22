-- Category of (small) categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Categories where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
-- open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude


-- Definition of Cat
module _ (ℓ ℓ' : Level) where
  open Category

  Cat : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  Cat .ob = Category ℓ ℓ'
  Cat .Hom[_,_] = Functor
  Cat .id = 𝟙⟨ _ ⟩
  Cat ._⋆_ G H = H ∘F G
  Cat .⋆IdL _ = F-lUnit
  Cat .⋆IdR _ = F-rUnit
  Cat .⋆Assoc _ _ _ = F-assoc
  Cat .isSetHom = {!   !}   -- is `Functor C D` a set?