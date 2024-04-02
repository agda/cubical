{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Instances.Int where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.Int

ℤAbGroup : AbGroup ℓ-zero
ℤAbGroup = Group→AbGroup ℤGroup +Comm
