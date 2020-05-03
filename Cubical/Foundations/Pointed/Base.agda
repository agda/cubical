{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Pointed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Structure using (typ) public
open import Cubical.Foundations.GroupoidLaws

Pointed : (ℓ : Level) → Type (ℓ-suc ℓ)
Pointed ℓ = TypeWithStr ℓ (λ x → x)

pt : ∀ {ℓ} (A∙ : Pointed ℓ) → typ A∙
pt = str

Pointed₀ = Pointed ℓ-zero

{- Pointed functions -}
_→∙_ : ∀{ℓ ℓ'} → (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
_→∙_ A B = Σ[ f ∈ (typ A → typ B) ] f (pt A) ≡ pt B

_→∙_∙ : ∀{ℓ ℓ'} → (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
A →∙ B ∙  = (A →∙ B) , (λ x → pt B) , refl

idfun∙ : ∀ {ℓ} (A : Pointed ℓ) → A →∙ A
idfun∙ A = (λ x → x) , refl
