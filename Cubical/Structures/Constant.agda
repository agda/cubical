{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.SIP

private
  variable
    ℓ ℓ' : Level

-- Constant structure

module _ (A : Type ℓ) where

  ConstantStructure : Type ℓ' → Type ℓ
  ConstantStructure _ = A

  ConstantIso : StrEquiv {ℓ'} ConstantStructure ℓ
  ConstantIso (_ , a) (_ , a') _ = a ≡ a'

  constantUnivalentStr : UnivalentStr {ℓ'} ConstantStructure ConstantIso
  constantUnivalentStr e = idEquiv _
