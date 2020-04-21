{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Pushout.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Data.Prod

open import Cubical.Data.Unit

open import Cubical.HITs.Susp.Base

data Pushout {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
             (f : A → B) (g : A → C) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  inl : B → Pushout f g
  inr : C → Pushout f g
  push : (a : A) → inl (f a) ≡ inr (g a)


---

_wedge_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Type (ℓ-max ℓ ℓ')
_wedge_ (A , ptA) (B , ptB) = Pushout {A = Unit} {B = A} {C = B} (λ {tt → ptA}) (λ {tt → ptB})

i∧ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → A wedge B → (typ A) × (typ B)
i∧ {A = A , ptA} {B = B , ptB} (inl x) = x , ptB
i∧ {A = A , ptA} {B = B , ptB} (inr x) = ptA , x
i∧ {A = A , ptA} {B = B , ptB} (push tt i) = ptA , ptB

_smash_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Type (ℓ-max ℓ ℓ')
_smash_ A B = Pushout {A = (A wedge B)} {B = Unit} {C = (typ A) × (typ B)} (λ _ → tt) i∧


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

PushoutSusp≃Susp : ∀ {ℓ} {A : Type ℓ} → PushoutSusp A ≃ Susp A
PushoutSusp≃Susp = isoToEquiv (iso PushoutSusp→Susp Susp→PushoutSusp Susp→PushoutSusp→Susp PushoutSusp→Susp→PushoutSusp)

PushoutSusp≡Susp : ∀ {ℓ} {A : Type ℓ} → PushoutSusp A ≡ Susp A
PushoutSusp≡Susp = isoToPath (iso PushoutSusp→Susp Susp→PushoutSusp Susp→PushoutSusp→Susp PushoutSusp→Susp→PushoutSusp)
