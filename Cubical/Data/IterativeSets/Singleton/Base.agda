{-# OPTIONS --lossy-unification #-}

module Cubical.Data.IterativeSets.Singleton.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ : Level
    x : V⁰ {ℓ}

singleton⁰ : V⁰ {ℓ} → V⁰ {ℓ}
singleton⁰ {ℓ} x = fromEmb E
  where
    E : Embedding (V⁰ {ℓ}) ℓ
    E .fst = Unit*
    E .snd .fst _ = x
    E .snd .snd = isEmbedding-isProp→isSet isPropUnit* isSetV⁰ _

El⁰singleton⁰IsUnit* : El⁰ (singleton⁰ x) ≡ Unit*
El⁰singleton⁰IsUnit* = refl

singleton⁰-is-singleton : {x z : V⁰ {ℓ}} → ((z ∈⁰ (singleton⁰ x)) ≃ (x ≡ z))
singleton⁰-is-singleton {x = x} {z = z} = isoToEquiv isom
  where
    isom : Iso (z ∈⁰ singleton⁰ x) (x ≡ z)
    isom .Iso.fun = snd
    isom .Iso.inv _ .fst = tt*
    isom .Iso.inv p .snd = p
    isom .Iso.ret _ = refl
    isom .Iso.sec _ = refl

singleton⁰-is-singleton-sym : {x z : V⁰ {ℓ}} → ((z ∈⁰ (singleton⁰ x)) ≃ (z ≡ x))
singleton⁰-is-singleton-sym {x = x} {z = z} = isoToEquiv isom 
  where
    isom : Iso (z ∈⁰ singleton⁰ x) (z ≡ x)
    isom .Iso.fun f = sym (snd f)
    isom .Iso.inv _ .fst = tt*
    isom .Iso.inv p .snd = sym p
    isom .Iso.ret _ = refl
    isom .Iso.sec _ = refl

singleton⁰≡singleton⁰ : {x y : V⁰ {ℓ}} → ((x ≡ y) ≃ (singleton⁰ x ≡ singleton⁰ y))
singleton⁰≡singleton⁰ {ℓ} {x} {y} = propBiimpl→Equiv (isSetV⁰ _ _)
                                                     (isSetV⁰ _ _)
                                                     (cong singleton⁰)
                                                     inv
  where
    inv : singleton⁰ x ≡ singleton⁰ y → x ≡ y
    inv p = singleton⁰-is-singleton .fst (≡V⁰-≃-≃V⁰ .fst p .snd y (tt* , refl))
