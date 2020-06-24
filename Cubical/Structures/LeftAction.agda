{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.LeftAction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP

open import Cubical.Structures.Auto

module _ {ℓ ℓ' : Level} (A : Type ℓ') where

  LeftActionStructure : Type ℓ → Type (ℓ-max ℓ ℓ')
  LeftActionStructure X = A → X → X

  LeftActionEquivStr = autoIso LeftActionStructure

  leftActionUnivalentStr : UnivalentStr _ LeftActionEquivStr
  leftActionUnivalentStr = autoSNS LeftActionStructure
