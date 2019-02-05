{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Conat.Base where

open import Cubical.Data.Unit
open import Cubical.Data.Sum

open import Cubical.Core.Everything

record Conat : Set
Prev = Unit ⊎ Conat
record Conat where
  coinductive
  constructor conat
  field prev : Prev
open Conat public

pattern zero  = inl tt
pattern suc n = inr n

succ : Conat → Conat
prev (succ a) = inr a

