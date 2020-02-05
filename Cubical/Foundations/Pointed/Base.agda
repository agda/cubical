{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Pointed.Base where

open import Cubical.Foundations.Prelude

Pointed : (ℓ : Level) → Type (ℓ-suc ℓ)
Pointed ℓ = Σ[ A ∈ Type ℓ ] A

typ : ∀ {ℓ} (A∙ : Pointed ℓ) → Type ℓ
typ = fst

pt : ∀ {ℓ} (A∙ : Pointed ℓ) → typ A∙
pt = snd
