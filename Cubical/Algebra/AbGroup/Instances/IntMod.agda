{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Instances.IntMod where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Fin.Arithmetic using (+ₘ-comm)

import Cubical.Algebra.Group.Instances.IntMod as Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Int

ℤAbGroup/_ : ℕ → AbGroup (ℓ-zero)
ℤAbGroup/ zero = ℤAbGroup
ℤAbGroup/ (suc n) = Group→AbGroup (Group.ℤGroup/ (suc n)) +ₘ-comm
