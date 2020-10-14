{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Number.Definitions where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic

open import SyntheticReals.Utils
open import SyntheticReals.MoreLogic.Definitions
open import SyntheticReals.MoreLogic.Properties
open import SyntheticReals.MorePropAlgebra.Definitions
open import SyntheticReals.MorePropAlgebra.Consequences
open import SyntheticReals.MorePropAlgebra.Structures
