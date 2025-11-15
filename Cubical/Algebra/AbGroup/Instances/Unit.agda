module Cubical.Algebra.AbGroup.Instances.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit renaming (Unit* to UnitType)

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Instances.Unit using (UnitGroup)
open import Cubical.Algebra.Group.Base using (GroupStr)

private
  variable
    ℓ : Level

open AbGroupStr
open IsAbGroup

UnitAbGroup : AbGroup ℓ
fst UnitAbGroup = UnitType
0g (snd UnitAbGroup) = tt*
_+_ (snd UnitAbGroup) = λ _ _ → tt*
- snd UnitAbGroup = λ _ → tt*
isGroup (isAbGroup (snd UnitAbGroup)) = GroupStr.isGroup (snd UnitGroup)
+Comm (isAbGroup (snd UnitAbGroup)) = λ _ _ → refl
