module Cubical.Foundations.Pointed.FunExt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties
open import Cubical.Foundations.Pointed.Homotopy

private
  variable
    ℓ ℓ' : Level

module _ {A : Pointed ℓ} {B : typ A → Type ℓ'} {ptB : B (pt A)} where

  -- pointed function extensionality
  funExt∙P : {f g : Π∙ A B ptB} → f ∙∼P g → f ≡ g
  funExt∙P (h , h∙) i .fst x = h x i
  funExt∙P (h , h∙) i .snd = h∙ i

  -- inverse of pointed function extensionality
  funExt∙P⁻ : {f g : Π∙ A B ptB} → f ≡ g → f ∙∼P g
  funExt∙P⁻ p .fst a i = p i .fst a
  funExt∙P⁻ p .snd i = p i .snd

  -- function extensionality is an isomorphism, PathP version
  funExt∙PIso : (f g : Π∙ A B ptB) → Iso (f ∙∼P g) (f ≡ g)
  Iso.fun (funExt∙PIso f g)  = funExt∙P {f = f} {g = g}
  Iso.inv (funExt∙PIso f g) = funExt∙P⁻ {f = f} {g = g}
  Iso.rightInv (funExt∙PIso f g) p i j = p j
  Iso.leftInv (funExt∙PIso f g) h _ = h

  -- transformed to equivalence
  funExt∙P≃ : (f g : Π∙ A B ptB) → (f ∙∼P g) ≃ (f ≡ g)
  funExt∙P≃ f g = isoToEquiv (funExt∙PIso f g)

  -- funExt∙≃ using the other kind of pointed homotopy
  funExt∙≃ : (f g : Π∙ A B ptB) → (f ∙∼ g) ≃ (f ≡ g)
  funExt∙≃ f g = compEquiv (∙∼≃∙∼P f g) (funExt∙P≃ f g)

  -- standard pointed function extensionality and its inverse
  funExt∙ : {f g : Π∙ A B ptB} → f ∙∼ g → f ≡ g
  funExt∙ {f = f} {g = g} = equivFun (funExt∙≃ f g)

  funExt∙⁻ : {f g : Π∙ A B ptB} → f ≡ g → f ∙∼ g
  funExt∙⁻ {f = f} {g = g} = equivFun (invEquiv (funExt∙≃ f g))
