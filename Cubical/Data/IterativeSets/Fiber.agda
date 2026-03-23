module Cubical.Data.IterativeSets.Fiber where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Data.IterativeSets.Identity

private
    variable
        ℓ : Level
        
fiber⁰ : {x y : V⁰ {ℓ}} (f : El⁰ x → El⁰ y) (b : El⁰ y) → V⁰ {ℓ}
fiber⁰ {x = x} {y = y} f b = Σ⁰ x λ a → Id⁰ y (f a) b

El⁰fiber⁰IsFiber : {x y : V⁰ {ℓ}} {f : El⁰ x → El⁰ y} {b : El⁰ y} → El⁰ (fiber⁰ {x = x} {y = y} f b) ≡ fiber f b
El⁰fiber⁰IsFiber = refl
