{-# OPTIONS --cubical --no-import-sorts #-}

-- Bundles w.r.t.
module SyntheticReals.Number.RBundles where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
