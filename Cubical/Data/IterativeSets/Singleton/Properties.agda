module Cubical.Data.IterativeSets.Singleton.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Nullary
open import Cubical.Data.Unit.Properties

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Singleton.Base
open import Cubical.Data.IterativeSets.Unit

private
  variable
    ℓ : Level
    x : V⁰ {ℓ}

empty⁰≢singleton⁰ : ¬ empty⁰ {ℓ} ≡ singleton⁰ x
empty⁰≢singleton⁰ p = ⊥*≢Unit* (cong El⁰ p)

singleton⁰≢empty⁰ : ¬ singleton⁰ x ≡ empty⁰ {ℓ}
singleton⁰≢empty⁰ p = Unit*≢⊥* (cong El⁰ p)

empty⁰≢unit⁰ : ¬ empty⁰ {ℓ} ≡ unit⁰ {ℓ}
empty⁰≢unit⁰ = empty⁰≢singleton⁰ {x = empty⁰}

unit⁰≢empty⁰ : ¬ unit⁰ {ℓ} ≡ empty⁰ {ℓ}
unit⁰≢empty⁰ = singleton⁰≢empty⁰ {x = empty⁰}
