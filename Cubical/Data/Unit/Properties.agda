{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Unit.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Unit.Base

isContrUnit : isContr Unit
isContrUnit = tt , λ {tt → refl}

isPropUnit : isProp Unit
isPropUnit _ _ i = tt -- definitionally equal to: isContr→isProp isContrUnit

isOfHLevelUnit : (n : ℕ) → isOfHLevel n Unit
isOfHLevelUnit n = isContr→isOfHLevel n isContrUnit

UnitToTypeId : ∀ {ℓ} (A : Type ℓ) → (Unit → A) ≡ A
UnitToTypeId A = isoToPath (iso (λ f → f tt) (λ a _ → a) (λ _ → refl) λ _ → refl)
