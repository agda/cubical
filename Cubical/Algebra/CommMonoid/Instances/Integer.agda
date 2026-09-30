module Cubical.Algebra.CommMonoid.Instances.Integer where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int as Int
open import Cubical.Algebra.CommMonoid

·IntCommMonoid : CommMonoid ℓ-zero
·IntCommMonoid = makeCommMonoid 1 Int._·_ Int.isSetℤ Int.·Assoc Int.·IdR Int.·Comm

+IntCommMonoid : CommMonoid ℓ-zero
+IntCommMonoid = makeCommMonoid 0 Int._+_ Int.isSetℤ Int.+Assoc (λ x → refl) Int.+Comm
