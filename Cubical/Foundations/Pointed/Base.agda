{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Pointed.Base where

open import Cubical.Foundations.Prelude

Pointed : (ℓ : Level) → Type (ℓ-suc ℓ)
Pointed ℓ = Σ[ A ∈ Type ℓ ] A

typ : ∀ {ℓ} (A∙ : Pointed ℓ) → Type ℓ
typ = fst

pt : ∀ {ℓ} (A∙ : Pointed ℓ) → typ A∙
pt = snd

{- Pointed functions -}
_→*_ : ∀{ℓ ℓ'} → (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
_→*_ A B = Σ (typ A → typ B) λ f → f (pt A) ≡ pt B

_→*_*  : ∀{ℓ ℓ'} → (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
A →* B *  = (A →* B) , (λ x → pt B) , refl
