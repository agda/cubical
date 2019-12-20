{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Unit.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Unit.Base

isPropUnit : isProp Unit
isPropUnit _ _ i = tt

isContrUnit : isContr Unit
isContrUnit = tt , λ {tt → refl}

isOfHLevelUnit : (n : ℕ) → isOfHLevel n Unit
isOfHLevelUnit 0       = isContrUnit
isOfHLevelUnit 1       = isPropUnit
isOfHLevelUnit (suc n) = hLevelSuc n Unit (isOfHLevelUnit n)
