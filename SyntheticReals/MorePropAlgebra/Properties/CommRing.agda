{-# OPTIONS --cubical --no-import-sorts  #-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Function.Base using (_∋_; _$_)

open import SyntheticReals.MorePropAlgebra.Bundles
import Cubical.Algebra.CommRing as Std

module SyntheticReals.MorePropAlgebra.Properties.CommRing {ℓ} (assumptions : CommRing {ℓ}) where
open CommRing assumptions renaming (Carrier to R)

import SyntheticReals.MorePropAlgebra.Properties.Ring
module Ring'Properties = SyntheticReals.MorePropAlgebra.Properties.Ring   (record { CommRing assumptions })
module Ring'           =                                           Ring   (record { CommRing assumptions })
(      Ring')          =                                           Ring ∋ (record { CommRing assumptions })


stdIsCommRing : Std.IsCommRing 0r 1r _+_ _·_ (-_)
stdIsCommRing .Std.IsCommRing.isRing = Ring'Properties.stdIsRing
stdIsCommRing .Std.IsCommRing.·-comm = ·-comm

stdCommRing : Std.CommRing {ℓ}
stdCommRing = record { CommRing assumptions ; isCommRing = stdIsCommRing }
--
-- module RingTheory' = Std.Theory stdRing
