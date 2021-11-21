-- The category Ab of abelian groups
{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.AbGroups where

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Categories.Category.Base
open import Cubical.Foundations.Prelude


module _ {ℓ : Level} where
  open Category

  Ab : Category (ℓ-suc ℓ) ℓ
  Ab .ob = AbGroup ℓ
  Ab .Hom[_,_] = AbGroupHom
  Ab .id = idGroupHom
  Ab ._⋆_ = compGroupHom
  Ab .⋆IdL f = GroupHom≡ refl
  Ab .⋆IdR f = GroupHom≡ refl
  Ab .⋆Assoc f g h = GroupHom≡ refl
  Ab .isSetHom = isSetGroupHom
