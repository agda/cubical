{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Pushout where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude
open import Cubical.Core.Glue

open import Cubical.Basics.Unit
open import Cubical.Basics.Equiv

open import Cubical.HITs.Susp

data Pushout {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
             (f : A → B) (g : A → C) : Set (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  inl : B → Pushout f g
  inr : C → Pushout f g
  push : (a : A) → inl (f a) ≡ inr (g a)


-- Suspension defined as a pushout

PushoutSusp : ∀ {ℓ} (A : Set ℓ) → Set ℓ
PushoutSusp A = Pushout {A = A} {B = Unit} {C = Unit} (λ _ → tt) (λ _ → tt)

PushoutSusp→Susp : ∀ {ℓ} {A : Set ℓ} → PushoutSusp A → Susp A
PushoutSusp→Susp (inl _) = north
PushoutSusp→Susp (inr _) = south
PushoutSusp→Susp (push a i) = merid a i

Susp→PushoutSusp : ∀ {ℓ} {A : Set ℓ} → Susp A → PushoutSusp A
Susp→PushoutSusp north = inl tt
Susp→PushoutSusp south = inr tt
Susp→PushoutSusp (merid a i) = push a i

Susp→PushoutSusp→Susp : ∀ {ℓ} {A : Set ℓ} (x : Susp A) →
                        PushoutSusp→Susp (Susp→PushoutSusp x) ≡ x
Susp→PushoutSusp→Susp north = refl
Susp→PushoutSusp→Susp south = refl
Susp→PushoutSusp→Susp (merid _ _) = refl

PushoutSusp→Susp→PushoutSusp : ∀ {ℓ} {A : Set ℓ} (x : PushoutSusp A) →
                               Susp→PushoutSusp (PushoutSusp→Susp x) ≡ x
PushoutSusp→Susp→PushoutSusp (inl _) = refl
PushoutSusp→Susp→PushoutSusp (inr _) = refl
PushoutSusp→Susp→PushoutSusp (push _ _) = refl

PushoutSusp≃Susp : ∀ {ℓ} {A : Set ℓ} → PushoutSusp A ≃ Susp A
PushoutSusp≃Susp = isoToEquiv PushoutSusp→Susp Susp→PushoutSusp
                              Susp→PushoutSusp→Susp PushoutSusp→Susp→PushoutSusp

PushoutSusp≡Susp : ∀ {ℓ} {A : Set ℓ} → PushoutSusp A ≡ Susp A
PushoutSusp≡Susp = isoToPath PushoutSusp→Susp Susp→PushoutSusp
                             Susp→PushoutSusp→Susp PushoutSusp→Susp→PushoutSusp
