{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

private
  variable
    ℓ' : Level

-- Constant structure

module _ {ℓ} (A : Type ℓ) where

  constant-structure : Type ℓ' → Type ℓ
  constant-structure _ = A

  constant-iso : StrIso {ℓ'} constant-structure ℓ
  constant-iso (_ , a) (_ , a') _ = a ≡ a'

  constant-is-SNS : SNS {ℓ'} constant-structure constant-iso
  constant-is-SNS e = idEquiv _
