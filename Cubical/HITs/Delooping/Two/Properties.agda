{-# OPTIONS --cubical --safe --no-import-sorts #-}

module Cubical.HITs.Delooping.Two.Properties where

open import Cubical.Functions.Involution

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool
open import Cubical.Data.FinSet.Binary

open import Cubical.HITs.Delooping.Two.Base

private
  variable
    ℓ : Level

module Embed where
  isSetIsPropDep : isOfHLevelDep {ℓ' = ℓ} 1 isSet
  isSetIsPropDep = isOfHLevel→isOfHLevelDep 1 (λ _ → isPropIsSet)

  notSet : PathP (λ i → isSet (notEq i)) isSetBool isSetBool
  notSet = isSetIsPropDep isSetBool isSetBool notEq

  notNot² : Square notEq refl refl notEq
  notNot² = involPath² notnot

  notNotSet
    : SquareP (λ i j → isSet (notNot² i j)) notSet refl refl notSet
  notNotSet = isPropDep→isSetDep'
                isSetIsPropDep
                (involPath² notnot)
                notSet refl refl notSet

  Code : Bℤ₂ → hSet ℓ-zero
  Code = Elim.rec
    (Bool , isSetBool)
    (λ i → notEq i , notSet i)
    (λ i j → λ where
      .fst → notNot² i j
      .snd → notNotSet i j)
    (isOfHLevelTypeOfHLevel 2)

  El : Bℤ₂ → Type₀
  El b = Code b .fst

module Binary where
  sem : Bℤ₂ → Binary _
  sem = Elim.rec Base Loop Loop² isGroupoidBinary
