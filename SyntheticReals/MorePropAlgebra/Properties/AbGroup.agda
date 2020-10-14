{-# OPTIONS --cubical --no-import-sorts  #-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Function.Base using (_∋_)
open import SyntheticReals.MorePropAlgebra.Bundles

import Cubical.Algebra.AbGroup as Std

module SyntheticReals.MorePropAlgebra.Properties.AbGroup {ℓ} (assumptions : AbGroup {ℓ}) where
open AbGroup assumptions renaming (Carrier to G)

import SyntheticReals.MorePropAlgebra.Properties.Group
module Group'Properties = SyntheticReals.MorePropAlgebra.Properties.Group   (record { AbGroup assumptions })
module Group'           =                                           Group   (record { AbGroup assumptions })
(      Group')          =                                           Group ∋ (record { AbGroup assumptions })

stdIsAbGroup : Std.IsAbGroup 0g _+_ (-_)
stdIsAbGroup  .Std.IsAbGroup.isGroup = Group'Properties.stdIsGroup
stdIsAbGroup  .Std.IsAbGroup.comm    = is-comm

stdAbGroup : Std.AbGroup {ℓ}
stdAbGroup = record { AbGroup assumptions ; isAbGroup = stdIsAbGroup }
