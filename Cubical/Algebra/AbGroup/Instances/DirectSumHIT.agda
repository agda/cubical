{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Instances.DirectSumHIT where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup

open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.DirectSum.DirectSumHIT.Properties

private variable
  ℓ ℓ' : Level

module _ (Idx : Type ℓ) (P : Idx → Type ℓ') (AGP : (r : Idx) → AbGroupStr (P r)) where

  open AbGroupStr

  ⊕HIT-AbGr : AbGroup (ℓ-max ℓ ℓ')
  fst ⊕HIT-AbGr = ⊕HIT Idx P AGP
  0g (snd ⊕HIT-AbGr) = neutral
  _+_ (snd ⊕HIT-AbGr) = _add_
  - snd ⊕HIT-AbGr = inv Idx P AGP
  isAbGroup (snd ⊕HIT-AbGr) = makeIsAbGroup trunc addAssoc addRid (rinv Idx P AGP) addComm
