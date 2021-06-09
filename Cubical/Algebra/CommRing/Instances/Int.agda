{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Instances.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_ )

ℤ : CommRing ℓ-zero
ℤ = makeCommRing 0 1 _+ℤ_ _·ℤ_ -ℤ_ isSetInt +Assoc (λ _ → refl) -Cancel +Comm ·Assoc ·Rid ·DistR+ ·Comm
