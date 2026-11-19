{-# OPTIONS --safe #-}
module Cubical.Homotopy.Serre.Pullback.IsPullback where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level

_▹_ : {A : Type ℓ} {B : Type ℓ} {C : Type ℓ} {f f' : B → C} (α : f ≡ f')
      (g : A → B) → f ∘ g ≡ f' ∘ g
α ▹ g = cong (_∘ g) α

module _ {B C D : Type ℓ} (f : B → D) (g : C → D) where
  SpanConeOn : Type ℓ → Type ℓ
  SpanConeOn A = Σ[ g' ∈ (A → B) ] Σ[ f' ∈ (A → C) ] f ∘ g' ≡ g ∘ f'

  precomp : {A A' : Type ℓ} → (A' → A) → SpanConeOn A → SpanConeOn A'
  fst (precomp h sco) = (fst sco) ∘ h
  fst (snd (precomp h sco)) = (fst (snd sco)) ∘ h
  snd (snd (precomp h sco)) = (snd (snd sco)) ▹ h

  module isPullback {P : Type ℓ} (g' : P → B) (f' : P → C) (α : f ∘ g' ≡ g ∘ f') where
    pullbackComparison : (E : Type ℓ) → (E → P) → SpanConeOn E
    pullbackComparison E h = precomp h (g' , f' , α)

    record isPullback : Type (ℓ-suc ℓ) where
      no-eta-equality
      field
        comparisonIsEquiv : (E : Type ℓ) → isEquiv (pullbackComparison E)
