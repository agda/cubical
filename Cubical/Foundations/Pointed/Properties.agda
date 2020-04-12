{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Pointed.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base
open import Cubical.Data.Sigma

Π∙ : ∀ {ℓ ℓ'} (A : Type ℓ) (B∙ : A → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
Π∙ A B∙ = (∀ a → typ (B∙ a)) , (λ a → pt (B∙ a))

Σ∙ : ∀ {ℓ ℓ'} (A∙ : Pointed ℓ) (B∙ : typ A∙ → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
Σ∙ A∙ B∙ = (Σ[ a ∈ typ A∙ ] typ (B∙ a)) , (pt A∙ , pt (B∙ (pt A∙)))

_×∙_ : ∀ {ℓ ℓ'} (A∙ : Pointed ℓ) (B∙ : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
A∙ ×∙ B∙ = ((typ A∙) × (typ B∙)) , (pt A∙ , pt B∙)
