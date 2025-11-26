module Cubical.Functions.Implicit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

implicit≃Explicit : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → ({a : A} → B a) ≃ ((a : A) → B a)
implicit≃Explicit = isoToEquiv isom
  where
  isom : Iso _ _
  Iso.fun isom f a = f
  Iso.inv isom f = f _
  Iso.sec isom f = funExt λ _ → refl
  Iso.ret isom f = implicitFunExt refl

