{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Structures.LeftAction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.Auto

module _ {ℓ ℓ' : Level} (A : Type ℓ') where

  left-action-structure : Type ℓ → Type ℓ'
  left-action-structure _ = A

  left-action-iso = autoIso left-action-structure

  Left-Action-is-SNS : SNS _ left-action-iso
  Left-Action-is-SNS = autoSNS left-action-structure
