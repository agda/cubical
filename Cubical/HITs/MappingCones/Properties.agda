{-# OPTIONS --safe #-}

module Cubical.HITs.MappingCones.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.HITs.Pushout

open import Cubical.HITs.MappingCones.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

PushoutUnit-iso-Cone : ∀ {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) → Iso (Pushout (const tt) f) (Cone f)
Iso.fun (PushoutUnit-iso-Cone f) (inl tt)   = hub
Iso.fun (PushoutUnit-iso-Cone f) (inr x)    = inj x
Iso.fun (PushoutUnit-iso-Cone f) (push x i) = spoke x i
Iso.inv (PushoutUnit-iso-Cone f) (inj x)     = inr x
Iso.inv (PushoutUnit-iso-Cone f) hub         = inl tt
Iso.inv (PushoutUnit-iso-Cone f) (spoke x i) = push x i
Iso.rightInv (PushoutUnit-iso-Cone f) (inj x)     = refl
Iso.rightInv (PushoutUnit-iso-Cone f) hub         = refl
Iso.rightInv (PushoutUnit-iso-Cone f) (spoke x i) = refl
Iso.leftInv (PushoutUnit-iso-Cone f) (inl tt)   = refl
Iso.leftInv (PushoutUnit-iso-Cone f) (inr x)    = refl
Iso.leftInv (PushoutUnit-iso-Cone f) (push x i) = refl

PushoutUnit≡Cone : ∀ {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) → Pushout (const tt) f ≡ Cone f
PushoutUnit≡Cone f = isoToPath (PushoutUnit-iso-Cone f)

ConesUnit-iso-Cone : ∀ {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) → Iso (Cones Unit (λ { tt → f })) (Cone f)
Iso.fun (ConesUnit-iso-Cone f) (inj x)        = inj x
Iso.fun (ConesUnit-iso-Cone f) (hub tt)       = hub
Iso.fun (ConesUnit-iso-Cone f) (spoke tt x i) = spoke x i
Iso.inv (ConesUnit-iso-Cone f) (inj x)     = inj x
Iso.inv (ConesUnit-iso-Cone f) hub         = hub tt
Iso.inv (ConesUnit-iso-Cone f) (spoke x i) = spoke tt x i
Iso.rightInv (ConesUnit-iso-Cone f) (inj x)     = refl
Iso.rightInv (ConesUnit-iso-Cone f) hub         = refl
Iso.rightInv (ConesUnit-iso-Cone f) (spoke x i) = refl
Iso.leftInv (ConesUnit-iso-Cone f) (inj x) = refl
Iso.leftInv (ConesUnit-iso-Cone f) (hub x) = refl
Iso.leftInv (ConesUnit-iso-Cone f) (spoke a x i) = refl

ConesUnit≡Cone : ∀ {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) → (Cones Unit (λ { tt → f })) ≡ (Cone f)
ConesUnit≡Cone f = isoToPath (ConesUnit-iso-Cone f)
