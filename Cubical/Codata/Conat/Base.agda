{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Conat.Base where

open import Cubical.Data.Unit
open import Cubical.Data.Sum

open import Cubical.Core.Everything

record Conat : Set
Conat′ = Unit ⊎ Conat
record Conat where
  coinductive
  constructor conat
  field force : Conat′
open Conat public

pattern zero  = inl tt
pattern suc n = inr n

succ : Conat → Conat
force (succ a) = suc a

succ′ : Conat′ → Conat′
succ′ n = suc (conat n)

pred′ : Conat′ → Conat′
pred′  zero   = zero
pred′ (suc x) = force x
