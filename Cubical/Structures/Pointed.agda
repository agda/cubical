{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Foundations.Pointed.Base

private
  variable
    ℓ : Level

-- Pointed types with SNS

pointed-structure : Type ℓ → Type ℓ
pointed-structure X = X

pointed-iso : StrIso pointed-structure ℓ
pointed-iso A B f = equivFun f (pt A) ≡ pt B

pointed-is-SNS : SNS {ℓ} pointed-structure pointed-iso
pointed-is-SNS f = invEquiv (ua-ungluePath-Equiv f)

pointed-SIP : (A B : Pointed ℓ) → A ≃[ pointed-iso ] B ≃ (A ≡ B)
pointed-SIP = SIP pointed-is-SNS

pointed-sip : (A B : Pointed ℓ) → A ≃[ pointed-iso ] B → (A ≡ B)
pointed-sip A B = equivFun (pointed-SIP A B) -- ≡ λ (e , p) i → ua e i , ua-gluePath e p i
