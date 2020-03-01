{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport

open import Cubical.Foundations.Pointed

open import Cubical.Foundations.SIP renaming (SNS₂ to SNS)

private
  variable
    ℓ : Level

-- Pointed types with SNS

pointed-structure : Type ℓ → Type ℓ
pointed-structure X = X

pointed-iso : StrIso pointed-structure ℓ
pointed-iso A B f = equivFun f (pt A) ≡ pt B

pointed-is-SNS : SNS {ℓ} pointed-structure pointed-iso
pointed-is-SNS A B f = transportEquiv (λ i → transportRefl (equivFun f (pt A)) i ≡ pt B)
