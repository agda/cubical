{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Power where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Product
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets

private
  variable
    ℓ ℓc ℓc' : Level

open Category

PowerCategory : (X : Type ℓ) (C : Category ℓc ℓc') → Category _ _
PowerCategory X C = ΠC X (λ _ → C)

PseudoYoneda : {C : Category ℓc ℓc'}
             → Functor C (PowerCategory (C .ob) (SET ℓc'))
PseudoYoneda {C = C} = Π-intro _ (λ _ → SET _) λ a → C [ a ,-]

isFaithfulPseudoYoneda : {C : Category ℓc ℓc'}
                       → Functor.isFaithful (PseudoYoneda {C = C})
isFaithfulPseudoYoneda {C = C} x y f g p =
  sym (C .⋆IdL f) ∙ (λ i → p i _ (C .id)) ∙ C .⋆IdL g
