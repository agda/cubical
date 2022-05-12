{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Instances.FreeAbGroup where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.FreeAbGroup
open import Cubical.Algebra.AbGroup

private variable
  ℓ : Level

module _ {A : Type ℓ} where

  FAGAbGroup : AbGroup ℓ
  FAGAbGroup = makeAbGroup {G = FreeAbGroup A} ε _·_ _⁻¹ trunc assoc identityᵣ invᵣ comm
