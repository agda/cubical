{-# OPTIONS --safe #-}

module Cubical.Relation.Binary.Extensionality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary.Base

module _ {ℓ ℓ'} {A : Type ℓ} (_≺_ : Rel A A ℓ') where

  ≡→≺Equiv : (x y : A) → x ≡ y → ∀ z → (z ≺ x) ≃ (z ≺ y)
  ≡→≺Equiv _ _ p z = substEquiv (z ≺_) p

  isWeaklyExtensional : Type _
  isWeaklyExtensional = ∀ {x y} → isEquiv (≡→≺Equiv x y)

  isPropIsWeaklyExtensional : isProp isWeaklyExtensional
  isPropIsWeaklyExtensional = isPropImplicitΠ2 λ _ _ → isPropIsEquiv _
