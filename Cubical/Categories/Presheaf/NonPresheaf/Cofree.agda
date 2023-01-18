{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.NonPresheaf.Cofree where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.NonPresheaf.Forget

open Category
open Functor
open NatTrans

private
  variable
    ℓ ℓ' ℓS : Level

cofreePresheaf : (C : Category ℓ ℓ')
  → NonPresheaf C ℓS → Presheaf C (ℓ-max (ℓ-max ℓ ℓ') ℓS)
fst (F-ob (cofreePresheaf C X) c) = (b : ob C) → C [ b , c ] → fst (X b)
snd (F-ob (cofreePresheaf C X) c) = isSetΠ (λ b → isSetΠ (λ _ → snd (X b)))
F-hom (cofreePresheaf C X) {d}{c} ψ x b φ = x b (φ ⋆⟨ C ⟩ ψ)
F-id (cofreePresheaf C X) {c} i x b φ = x b (⋆IdR C φ i)
F-seq (cofreePresheaf C X) {e}{d}{c} ω ψ i x b φ = x b (⋆Assoc C φ ψ ω (~ i))

CofreePresheaf : (C : Category ℓ ℓ')
  → Functor (NonPresheafCategory C ℓS) (PresheafCategory C (ℓ-max (ℓ-max ℓ ℓ') ℓS))
F-ob (CofreePresheaf C) = cofreePresheaf C
N-ob (F-hom (CofreePresheaf C) {X} {Y} f) c x b φ = f b (x b φ)
N-hom (F-hom (CofreePresheaf C) {X} {Y} f) {c}{c'} g = refl
F-id (CofreePresheaf C) {X} = makeNatTransPath refl
F-seq (CofreePresheaf C) {X}{Y}{Z} f g = makeNatTransPath refl

-- Prove relative adjunction w.r.t. a level-lift between SETs?
