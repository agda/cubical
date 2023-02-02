{-# OPTIONS --safe #-}

module Cubical.Relation.Binary.Extensionality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Relation.Binary.Base

module _ {ℓ ℓ'} {A : Type ℓ} (_≺_ : Rel A A ℓ') where

  ≡→≺Equiv : (x y : A) → x ≡ y → ∀ z → (z ≺ x) ≃ (z ≺ y)
  ≡→≺Equiv _ _ p z = substEquiv (z ≺_) p

  isWeaklyExtensional : Type _
  isWeaklyExtensional = ∀ x y → isEquiv (≡→≺Equiv x y)

  isPropIsWeaklyExtensional : isProp isWeaklyExtensional
  isPropIsWeaklyExtensional = isPropΠ2 λ _ _ → isPropIsEquiv _

  {- HoTT Definition 10.3.9 has extensionality defined under these terms.
     We prove that under those conditions, it implies our more hlevel-friendly
     definition.
  -}

  ≺Equiv→≡→IsWeaklyExtensional : isSet A → BinaryRelation.isPropValued _≺_
                             → ((x y : A) → (∀ z → (z ≺ x) ≃ (z ≺ y)) → x ≡ y)
                             → isWeaklyExtensional
  ≺Equiv→≡→IsWeaklyExtensional setA prop f a b
    = propBiimpl→Equiv (setA a b)
                       (isPropΠ (λ z → isOfHLevel≃ 1 (prop z a)
                                                      (prop z b)))
                       (≡→≺Equiv a b)
                       (f a b) .snd
