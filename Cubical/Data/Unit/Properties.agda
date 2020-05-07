{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Unit.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Unit.Base
open import Cubical.Data.Prod.Base

isContrUnit : isContr Unit
isContrUnit = tt , λ {tt → refl}

isPropUnit : isProp Unit
isPropUnit _ _ i = tt -- definitionally equal to: isContr→isProp isContrUnit

isOfHLevelUnit : (n : ℕ) → isOfHLevel n Unit
isOfHLevelUnit n = isContr→isOfHLevel n isContrUnit

diagonal-unit : Unit ≡ Unit × Unit
diagonal-unit = isoToPath (iso (λ x → tt , tt) (λ x → tt) (λ {(tt , tt) i → tt , tt}) λ {tt i → tt})
  where open import Cubical.Foundations.Isomorphism
