module Cubical.Data.Empty.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Empty.Base

isProp⊥ : isProp ⊥
isProp⊥ ()

isProp⊥* : ∀ {ℓ} → isProp {ℓ} ⊥*
isProp⊥* _ ()

isContr⊥→A : ∀ {ℓ} {A : Type ℓ} → isContr (⊥ → A)
fst isContr⊥→A ()
snd isContr⊥→A f i ()

isContrΠ⊥ : ∀ {ℓ} {A : ⊥ → Type ℓ} → isContr ((x : ⊥) → A x)
fst isContrΠ⊥ ()
snd isContrΠ⊥ f i ()

isContrΠ⊥* : ∀ {ℓ ℓ'} {A : ⊥* {ℓ} → Type ℓ'} → isContr ((x : ⊥*) → A x)
fst isContrΠ⊥* ()
snd isContrΠ⊥* f i ()

uninhabEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (A → ⊥) → (B → ⊥) → A ≃ B
uninhabEquiv ¬a ¬b = isoToEquiv isom
  where
  open Iso
  isom : Iso _ _
  isom .fun a = rec (¬a a)
  isom .inv b = rec (¬b b)
  isom .rightInv b = rec (¬b b)
  isom .leftInv a = rec (¬a a)
