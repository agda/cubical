
module Cubical.Modalities.Instances.Open where

open import Cubical.Modalities.Modality

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (isoToIsEquiv; iso)
open import Cubical.Foundations.Function using (const)
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Foundations.Structure using (⟨_⟩)


module _ {ℓ : Level} (X : hProp ℓ) where

  openModality : Modality ℓ

  -- We want to use ◯ and η as soon as we defined them.
  open Modality openModality

  Modality.◯ openModality A = ⟨ X ⟩ → A
  Modality.η openModality = const

  Modality.isModal openModality A = isEquiv (η {A = A})
  Modality.isPropIsModal openModality = isPropIsEquiv _

  Modality.◯-isModal openModality =
    isoToIsEquiv
      (iso
        η
        (λ f x → f x x)
        (λ f → λ i x x' → f (snd X x' x i) x')
        (λ f → refl))

  Modality.◯-elim openModality {B = B} B-modal f g =
    invIsEq
      (B-modal g)
      (λ x → subst B (λ i x' → g (snd X x x' i)) (f (g x)))

  Modality.◯-elim-β openModality {B = B} B-modal f a =
      cong
        (invEq eq)
        (funExt (λ _ → transportRefl _))
    ∙ retEq eq (f a)
    where
    eq : B (const a) ≃ ◯ (B (const a))
    eq = const , B-modal (const a)

  Modality.◯-=-isModal openModality f f' =
    isoToIsEquiv
      (iso
        η
        (λ p → λ i x → p x i x)
        (λ p → λ i x j x' → p (snd X x' x i) j x')
        (λ p → refl))
