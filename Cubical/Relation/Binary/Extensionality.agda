{-# OPTIONS --safe #-}

module Cubical.Relation.Binary.Extensionality where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary.Base

module _ {ℓ ℓ'} {A : Type ℓ} (_≺_ : Rel A A ℓ') where
  isWeaklyExtensional : Type _
  isWeaklyExtensional = ∀ {x y} → (∀ {z} → (z ≺ x → z ≺ y) × (z ≺ y → z ≺ x)) → x ≡ y

  isWeaklyExtensional-isProp : isSet A → isProp isWeaklyExtensional
  isWeaklyExtensional-isProp A-isSet wext₁ wext₂ i ≺x⇔≺y =
    A-isSet _ _ (wext₁ ≺x⇔≺y) (wext₂ ≺x⇔≺y) i
