{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Empty.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Empty.Base

isProp⊥ : isProp ⊥
isProp⊥ ()

isContr⊥→A : ∀ {ℓ} {A : Type ℓ} → isContr (⊥ → A)
fst isContr⊥→A ()
snd isContr⊥→A f i ()

uninhabEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (A → ⊥) → (B → ⊥) → A ≃ B
uninhabEquiv ¬a ¬b = isoToEquiv
  (λ a → rec (¬a a))
  (λ b → rec (¬b b))
  (λ b → rec (¬b b))
  (λ a → rec (¬a a))
