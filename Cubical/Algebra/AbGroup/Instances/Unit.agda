{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Instances.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit renaming (Unit* to UnitType)

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Instances.Unit using () renaming (Unit* to UnitGroup*)
open import Cubical.Algebra.Group.Base using (GroupStr)

private
  variable
    ℓ : Level

open AbGroupStr
open IsAbGroup

Unit* : AbGroup ℓ
fst Unit* = UnitType
0g (snd Unit*) = tt*
_+_ (snd Unit*) = λ _ _ → tt*
- snd Unit* = λ _ → tt*
isGroup (isAbGroup (snd Unit*)) = GroupStr.isGroup (snd UnitGroup*)
comm (isAbGroup (snd Unit*)) = λ _ _ → refl
