{-# OPTIONS --safe #-}

module Cubical.Modalities.Instances.Open where

open import Cubical.Modalities.Modality

-- TODO: imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty
open import Cubical.Data.Sigma


module _ {ℓ : Level} (X : hProp ℓ) where

  --  A → (X → A)

  openModality : Modality ℓ
  Modality.isModal openModality A = isEquiv {A = A} {B = ⟨ X ⟩ → A} const
  Modality.isPropIsModal openModality = isPropIsEquiv _
  Modality.◯ openModality A = ⟨ X ⟩ → A
  Modality.◯-isModal openModality = {!!}
  Modality.η openModality = const
  Modality.◯-elim openModality {B = B} B-modal f g =
    -- TODO: do better?
    invIsEq (B-modal g) {!!}
--            (λ x → subst B (funExt (λ _ → cong g (snd X _ _))) (f (g x)))
  Modality.◯-elim-β openModality = {!!}
  Modality.◯-=-isModal openModality = {!!}
