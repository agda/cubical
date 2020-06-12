{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Structures.LeftAction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.Macro

module _ {ℓ} (A : Type ℓ) where

  left-action-desc = param A (recvar var)

  open Macro ℓ left-action-desc public renaming
    ( structure to left-action-structure
    ; iso to left-action-iso
    ; isSNS to Left-Action-is-SNS
    )
