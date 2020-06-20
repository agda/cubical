{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Pointed.FunExt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties
open import Cubical.Foundations.Pointed.Homotopy

module _ {ℓ ℓ'} {A : Pointed ℓ} {B : typ A → Type ℓ'} {ptB : B (pt A)} where

  -- pointed function extensionality
  funExt∙P : {f g : Π∙ A B ptB} → f ∙∼P g → f ≡ g
  funExt∙P (h , h∙) i = (λ x → h x i) , h∙ i

  -- inverse of pointed function extensionality
  funExt∙P⁻ : {f g : Π∙ A B ptB} → f ≡ g → f ∙∼P g
  funExt∙P⁻ p = (λ a i → p i .fst a) , λ i → p i .snd

  -- function extensionality is an isomorphism, PathP version
  funExt∙PIso : (f g : Π∙ A B ptB) → Iso (f ∙∼P g) (f ≡ g)
  funExt∙PIso f g =
    iso (funExt∙P {f = f} {g = g})
        (funExt∙P⁻ {f = f} {g = g})
        (λ p i j → (λ a → p j .fst a) , λ k → p j .snd k)
        λ h _ → h

  -- transformed to equivalence
  funExt∙P≃ : (f g : Π∙ A B ptB) → (f ∙∼P g) ≃ (f ≡ g)
  funExt∙P≃ f g = isoToEquiv (funExt∙PIso f g)
