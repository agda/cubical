-- The category Ab of abelian groups
{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.AbGroups where

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Categories.Category.Base
open import Cubical.Foundations.Prelude


module _ {ℓ : Level} where
  open Category

  AbGroupCategory : Category (ℓ-suc ℓ) ℓ
  AbGroupCategory .ob = AbGroup ℓ
  AbGroupCategory .Hom[_,_] = AbGroupHom
  AbGroupCategory .id = idGroupHom
  AbGroupCategory ._⋆_ = compGroupHom
  AbGroupCategory .⋆IdL f = GroupHom≡ refl
  AbGroupCategory .⋆IdR f = GroupHom≡ refl
  AbGroupCategory .⋆Assoc f g h = GroupHom≡ refl
  AbGroupCategory .isSetHom = isSetGroupHom
