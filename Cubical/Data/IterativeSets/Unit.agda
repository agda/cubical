module Cubical.Data.IterativeSets.Unit where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Data.Unit

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Singleton
open import Cubical.Data.IterativeSets.Empty

private
  variable
    ℓ : Level
    z : V⁰ {ℓ}

unit⁰ : V⁰ {ℓ}
unit⁰ = singleton⁰ empty⁰

El⁰unit⁰IsUnit* : El⁰ {ℓ} unit⁰ ≡ Unit* {ℓ}
El⁰unit⁰IsUnit* = refl

unit⁰-is-singleton-empty⁰ : ((z ∈⁰ unit⁰) ≃ (empty⁰ ≡ z))
unit⁰-is-singleton-empty⁰ = singleton⁰-is-singleton
