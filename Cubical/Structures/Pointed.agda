{-

Pointed structure: X ↦ X

-}
{-# OPTIONS --safe #-}
module Cubical.Structures.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP

open import Cubical.Foundations.Pointed.Base

private
  variable
    ℓ : Level

-- Structured isomorphisms

PointedStructure : Type ℓ → Type ℓ
PointedStructure X = X

PointedEquivStr : StrEquiv PointedStructure ℓ
PointedEquivStr A B f = equivFun f (pt A) ≡ pt B

pointedUnivalentStr : UnivalentStr {ℓ} PointedStructure PointedEquivStr
pointedUnivalentStr f = invEquiv (ua-ungluePath-Equiv f)

pointedSIP : (A B : Pointed ℓ) → A ≃[ PointedEquivStr ] B ≃ (A ≡ B)
pointedSIP = SIP pointedUnivalentStr

pointed-sip : (A B : Pointed ℓ) → A ≃[ PointedEquivStr ] B → (A ≡ B)
pointed-sip A B = equivFun (pointedSIP A B) -- ≡ λ (e , p) i → ua e i , ua-gluePath e p i

pointedEquivAction : EquivAction {ℓ} PointedStructure
pointedEquivAction e = e

pointedTransportStr : TransportStr {ℓ} pointedEquivAction
pointedTransportStr e s = sym (transportRefl _)
