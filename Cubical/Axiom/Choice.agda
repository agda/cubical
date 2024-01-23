{-# OPTIONS --safe #-}

{-
This file contains a definition of the n-level axiom of coice,
i.e. the statment that the canonical map

∥ Πₐ Bₐ ∥ₙ → (Πₐ ∥ Bₐ ∥ₙ)

is an equivalence.
-}

module Cubical.Axiom.Choice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin as FN
open import Cubical.Data.Nat.Order

open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ' ℓ'' : Level

choiceMap : {A : Type ℓ} {B : A → Type ℓ'} (n : ℕ)
  → hLevelTrunc n ((a : A) → B a)
  → (a : A) → hLevelTrunc n (B a)
choiceMap n =
  TR.rec (isOfHLevelΠ n (λ _ → isOfHLevelTrunc n))
         λ f a → ∣ f a ∣ₕ

-- n-level axiom of choice
satAC : (ℓ' : Level) (n : ℕ) (A : Type ℓ)  → Type (ℓ-max ℓ (ℓ-suc ℓ'))
satAC ℓ' n A = (B : A → Type ℓ') → isEquiv (choiceMap {A = A} {B} n)

-- Version of (propositional) AC with ∃
AC∃-map : {A : Type ℓ} {B : A → Type ℓ'}
     {C : (a : A) → B a → Type ℓ''}
  → ∃[ f ∈ ((a : A) → B a) ] ((a : _) → C a (f a))
  → ((a : A) → ∃ (B a) (C a))
AC∃-map =
  PT.rec (isPropΠ (λ _ → squash₁))
    λ f → λ a → ∣ f .fst a , f .snd a ∣₁

satAC∃ : ∀ {ℓ} (ℓ' ℓ'' : Level) (A : Type ℓ) → Type _
satAC∃ ℓ' ℓ'' A = (B : A → Type ℓ') (C : (a : A) → B a → Type ℓ'')
  → isEquiv (AC∃-map {B = B} {C = C})

satAC→satAC∃ : {A : Type ℓ}
  → satAC (ℓ-max ℓ' ℓ'') (suc zero) A → satAC∃ ℓ' ℓ'' A
satAC→satAC∃ F B C = propBiimpl→Equiv squash₁ (isPropΠ (λ _ → squash₁))
  _
  (λ f → invEq propTrunc≃Trunc1 (TR.map (λ f → fst ∘ f , λ a → f a .snd )
          (invEq (_ , F (λ x → Σ (B x) (C x))) λ a → fst propTrunc≃Trunc1 (f a)))) .snd

-- All types satisfy (-2) level axiom of choice
satAC₀ : {A : Type ℓ} → satAC ℓ' 0 A
satAC₀ B = isoToIsEquiv (iso (λ _ _ → tt*) (λ _ → tt*) (λ _ → refl) λ _ → refl)
