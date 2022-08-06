{-# OPTIONS --safe #-}

module Cubical.Modalities.Instances.Open where

open import Cubical.Modalities.Modality

-- TODO: imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty
open import Cubical.Data.Sigma


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
--        (λ f → funExt λ x → funExt λ x' → cong (λ x'' → f x'' x') (snd X x' x))
        (λ f → refl))

  Modality.◯-elim openModality {B = B} B-modal f g =
    invIsEq
      (B-modal g)
      (λ x → subst B (λ i x' → g (snd X x x' i)) (f (g x)))
--      (λ x → subst B (funExt (λ _ → cong g (snd X _ _))) (f (g x)))

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
--        (λ p → funExt (λ x → cong (λ f → f x) (p x)))
        (λ p → λ i x j x' → p (snd X x' x i) j x')
        (λ p → refl))
