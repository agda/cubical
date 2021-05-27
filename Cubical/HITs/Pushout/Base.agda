{-# OPTIONS --safe #-}
module Cubical.HITs.Pushout.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit

open import Cubical.HITs.Susp.Base

data Pushout {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
             (f : A → B) (g : A → C) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  inl : B → Pushout f g
  inr : C → Pushout f g
  push : (a : A) → inl (f a) ≡ inr (g a)

-- cofiber (equivalent to Cone in Cubical.HITs.MappingCones.Base)
cofib : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type _
cofib f = Pushout (λ _ → tt) f

cfcod : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → B → cofib f
cfcod f = inr

-- Suspension defined as a pushout

PushoutSusp : ∀ {ℓ} (A : Type ℓ) → Type ℓ
PushoutSusp A = Pushout {A = A} {B = Unit} {C = Unit} (λ _ → tt) (λ _ → tt)

PushoutSusp→Susp : ∀ {ℓ} {A : Type ℓ} → PushoutSusp A → Susp A
PushoutSusp→Susp (inl _) = north
PushoutSusp→Susp (inr _) = south
PushoutSusp→Susp (push a i) = merid a i

Susp→PushoutSusp : ∀ {ℓ} {A : Type ℓ} → Susp A → PushoutSusp A
Susp→PushoutSusp north = inl tt
Susp→PushoutSusp south = inr tt
Susp→PushoutSusp (merid a i) = push a i

Susp→PushoutSusp→Susp : ∀ {ℓ} {A : Type ℓ} (x : Susp A) →
                        PushoutSusp→Susp (Susp→PushoutSusp x) ≡ x
Susp→PushoutSusp→Susp north = refl
Susp→PushoutSusp→Susp south = refl
Susp→PushoutSusp→Susp (merid _ _) = refl

PushoutSusp→Susp→PushoutSusp : ∀ {ℓ} {A : Type ℓ} (x : PushoutSusp A) →
                               Susp→PushoutSusp (PushoutSusp→Susp x) ≡ x
PushoutSusp→Susp→PushoutSusp (inl _) = refl
PushoutSusp→Susp→PushoutSusp (inr _) = refl
PushoutSusp→Susp→PushoutSusp (push _ _) = refl

PushoutSuspIsoSusp : ∀ {ℓ} {A : Type ℓ} → Iso (PushoutSusp A) (Susp A)
Iso.fun PushoutSuspIsoSusp = PushoutSusp→Susp
Iso.inv PushoutSuspIsoSusp = Susp→PushoutSusp
Iso.rightInv PushoutSuspIsoSusp = Susp→PushoutSusp→Susp
Iso.leftInv PushoutSuspIsoSusp = PushoutSusp→Susp→PushoutSusp


PushoutSusp≃Susp : ∀ {ℓ} {A : Type ℓ} → PushoutSusp A ≃ Susp A
PushoutSusp≃Susp = isoToEquiv PushoutSuspIsoSusp

PushoutSusp≡Susp : ∀ {ℓ} {A : Type ℓ} → PushoutSusp A ≡ Susp A
PushoutSusp≡Susp = isoToPath PushoutSuspIsoSusp
