module Cubical.Algebra.AbGroup.Instances.Fast.Int where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Fast.Int
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Instances.Fast.Int

ℤAbGroup : AbGroup ℓ-zero
ℤAbGroup = Group→AbGroup ℤGroup +Comm
