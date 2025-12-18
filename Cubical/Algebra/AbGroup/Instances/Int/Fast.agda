module Cubical.Algebra.AbGroup.Instances.Int.Fast where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int.Fast
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Instances.Int.Fast

ℤAbGroup : AbGroup ℓ-zero
ℤAbGroup = Group→AbGroup ℤGroup +Comm
