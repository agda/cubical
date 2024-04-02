{-# OPTIONS --safe #-}

module Cubical.Relation.Binary.Extensionality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Relation.Binary.Base

open import Cubical.Data.Sigma

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

  ≺Equiv→≡→isWeaklyExtensional : isSet A → BinaryRelation.isPropValued _≺_
                             → ((x y : A) → (∀ z → ((z ≺ x) ≃ (z ≺ y))) → x ≡ y)
                             → isWeaklyExtensional
  ≺Equiv→≡→isWeaklyExtensional setA prop f a b
    = propBiimpl→Equiv (setA a b)
                       (isPropΠ (λ z → isOfHLevel≃ 1
                                                   (prop z a)
                                                   (prop z b)))
                       (≡→≺Equiv a b)
                       (λ g → f a b λ z → g z) .snd

  ≺×→≡→isWeaklyExtensional : isSet A → BinaryRelation.isPropValued _≺_
                            → ((x y : A) → (∀ z → ((z ≺ x) → (z ≺ y))
                                                × ((z ≺ y) → (z ≺ x))) → x ≡ y)
                            → isWeaklyExtensional
  ≺×→≡→isWeaklyExtensional setA prop f a b
    = propBiimpl→Equiv (setA a b)
                       (isPropΠ (λ z → isOfHLevel≃ 1
                                                   (prop z a)
                                                   (prop z b)))
                       (≡→≺Equiv a b)
                       (λ g → f a b λ z → (g z .fst) , invEq (g z)) .snd

  isWeaklyExtensional→≺Equiv→≡ : isWeaklyExtensional
                                → (x y : A) → (∀ z → (z ≺ x) ≃ (z ≺ y)) → x ≡ y
  isWeaklyExtensional→≺Equiv→≡ weak x y
    = invIsEq (weak x y)
