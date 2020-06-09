{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Structures.LeftAction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.Pointed
open import Cubical.Structures.NAryOp
open import Cubical.Structures.Parameterized

private
  variable
   ℓ ℓ' : Level

module _ (A : Type ℓ) where

  left-action-structure : Type ℓ → Type ℓ
  left-action-structure =
   parameterized-structure A λ _ → nAryFun-structure 1 pointed-structure

  left-action-iso : StrIso left-action-structure ℓ
  left-action-iso =
   parameterized-iso A λ _ → unaryFunIso pointed-iso

  Left-Action-is-SNS : SNS {ℓ} left-action-structure left-action-iso
  Left-Action-is-SNS =
   Parameterized-is-SNS A
     (λ _ → unaryFunIso pointed-iso)
     (λ _ → unaryFunSNS pointed-iso pointed-is-SNS)
