{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Instances.Direct-Sum where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup

open import Cubical.Algebra.Direct-Sum.Base
open import Cubical.Algebra.Direct-Sum.Properties

private variable
  ℓ : Level

module _ (Idx : Type ℓ) (P : Idx → Type ℓ) (AGP : (r : Idx) → AbGroupStr (P r)) where

  open AbGroupStr

  ⊕-AbGr : AbGroup ℓ
  fst ⊕-AbGr = ⊕ Idx P AGP
  0g (snd ⊕-AbGr) = neutral
  _+_ (snd ⊕-AbGr) = _add_
  - snd ⊕-AbGr = inv Idx P AGP
  isAbGroup (snd ⊕-AbGr) = makeIsAbGroup trunc addAssoc addRid (rinv Idx P AGP) addComm
