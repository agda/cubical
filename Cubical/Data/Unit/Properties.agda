{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Unit.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit.Base

isPropUnit : isProp Unit
isPropUnit _ _ i = tt

isContrUnit : isContr Unit
isContrUnit = tt , λ {tt → refl}
