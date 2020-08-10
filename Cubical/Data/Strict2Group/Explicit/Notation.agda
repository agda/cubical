{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Strict2Group.Explicit.Notation where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Data.Group.Base

module S2GBaseNotation {ℓ : Level} (C₀ C₁ : Group ℓ) (s t : morph C₁ C₀) (i : morph C₀ C₁) (∘ : (g f : Group.type C₁) → (s .fst) g ≡ (t .fst f) → Group.type C₁) where

  -- group operations of the object group
  TC₀ = Group.type C₀
  1₀ = isGroup.id (Group.groupStruc C₀)
  _∙₀_ = isGroup.comp (Group.groupStruc C₀)
  C₀⁻¹ = isGroup.inv (Group.groupStruc C₀)
  rUnit₀ = isGroup.rUnit (Group.groupStruc C₀)
  lUnit₀ = isGroup.lUnit (Group.groupStruc C₀)
  assoc₀ = isGroup.assoc (Group.groupStruc C₀)
  lCancel₀ = isGroup.lCancel (Group.groupStruc C₀)
  rCancel₀ = isGroup.lCancel (Group.groupStruc C₀)

  -- group operation of the morphism group
  TC₁ = Group.type C₁
  1₁ = isGroup.id (Group.groupStruc C₁)
  C₁⁻¹ = isGroup.inv (Group.groupStruc C₁)
  _∙₁_ = isGroup.comp (Group.groupStruc C₁)
  rUnit₁ = isGroup.rUnit (Group.groupStruc C₁)
  lUnit₁ = isGroup.lUnit (Group.groupStruc C₁)
  assoc₁ = isGroup.assoc (Group.groupStruc C₁)
  lCancel₁ = isGroup.lCancel (Group.groupStruc C₁)
  rCancel₁ = isGroup.lCancel (Group.groupStruc C₁)

  -- interface for source, target and identity map
  src = fst s
  src∙₁ = snd s
  tar = fst t
  tar∙₁ = snd t
  id = fst i
  id∙₀ = snd i

  ∙c : {g f g' f' : Group.type C₁} → (coh1 : s .fst g ≡ t .fst f) → (coh2 : s .fst g' ≡ t .fst f') → s .fst (g ∙₁ g') ≡ t .fst (f ∙₁ f')
  ∙c {g} {f} {g'} {f'} coh1 coh2 = (s .snd g g') ∙ ((cong (_∙₀ (s .fst g')) coh1) ∙ (cong ((t .fst f) ∙₀_) coh2) ∙ (sym (t .snd f f')))

  -- for two morphisms the condition for them to be composable
  CohCond : (g f : TC₁) → Type ℓ
  CohCond g f = src g ≡ tar f
