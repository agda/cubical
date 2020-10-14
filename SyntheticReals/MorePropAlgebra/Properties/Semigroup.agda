{-# OPTIONS --cubical --no-import-sorts  #-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
import Cubical.Algebra.Semigroup as Std
open import SyntheticReals.MorePropAlgebra.Bundles

module SyntheticReals.MorePropAlgebra.Properties.Semigroup {ℓ} (assumptions : Semigroup {ℓ}) where
open Semigroup assumptions renaming (Carrier to G)

stdIsSemigroup : Std.IsSemigroup _·_
stdIsSemigroup  .Std.IsSemigroup.is-set = is-set
stdIsSemigroup  .Std.IsSemigroup.assoc  = is-assoc

stdSemigroup : Std.Semigroup {ℓ}
stdSemigroup = record { Semigroup assumptions ; isSemigroup = stdIsSemigroup }
