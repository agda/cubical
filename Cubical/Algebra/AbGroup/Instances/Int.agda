{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Instances.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int using (+Comm)

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Instances.Int

ℤAbGroup : AbGroup (ℓ-zero)
ℤAbGroup = Group→AbGroup ℤGroup +Comm
