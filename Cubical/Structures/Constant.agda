{-

Constant structure: _ ↦ A

-}
{-# OPTIONS --safe #-}
module Cubical.Structures.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.SIP

private
  variable
    ℓ ℓ' : Level

-- Structured isomorphisms

module _ (A : Type ℓ') where

  ConstantStructure : Type ℓ → Type ℓ'
  ConstantStructure _ = A

  ConstantEquivStr : StrEquiv {ℓ} ConstantStructure ℓ'
  ConstantEquivStr (_ , a) (_ , a') _ = a ≡ a'

  constantUnivalentStr : UnivalentStr {ℓ} ConstantStructure ConstantEquivStr
  constantUnivalentStr e = idEquiv _

  constantEquivAction : EquivAction {ℓ} ConstantStructure
  constantEquivAction e = idEquiv _

  constantTransportStr : TransportStr {ℓ} constantEquivAction
  constantTransportStr e _ = sym (transportRefl _)
