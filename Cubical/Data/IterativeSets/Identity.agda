module Cubical.Data.IterativeSets.Identity where

open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty

private
    variable
        ℓ : Level

Id⁰ : (x : V⁰ {ℓ}) (a b : El⁰ x) → V⁰ {ℓ}
Id⁰ x a b = fromEmb E
  where
    E : Embedding V⁰ _
    E .fst = a ≡ b
    E .snd .fst _ = empty⁰
    E .snd .snd = isEmbedding-isProp→isSet (isSetEl⁰ x a b) isSetV⁰ (E .snd .fst)

El⁰Id⁰IsId : {x : V⁰ {ℓ}} {a b : El⁰ x} → El⁰ (Id⁰ x a b) ≡ (a ≡ b)
El⁰Id⁰IsId = refl
