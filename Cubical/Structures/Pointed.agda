{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP

open import Cubical.Foundations.Pointed.Base

private
  variable
    ℓ : Level

-- Pointed types with SNS

PointedStructure : Type ℓ → Type ℓ
PointedStructure X = X

PointedIso : StrIso PointedStructure ℓ
PointedIso A B f = equivFun f (pt A) ≡ pt B

pointedUnivalentStr : UnivalentStr {ℓ} PointedStructure PointedIso
pointedUnivalentStr f = invEquiv (ua-ungluePath-Equiv f)

pointedSIP : (A B : Pointed ℓ) → A ≃[ PointedIso ] B ≃ (A ≡ B)
pointedSIP = SIP pointedUnivalentStr

pointed-sip : (A B : Pointed ℓ) → A ≃[ PointedIso ] B → (A ≡ B)
pointed-sip A B = equivFun (pointedSIP A B) -- ≡ λ (e , p) i → ua e i , ua-gluePath e p i
